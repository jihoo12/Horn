//! Hash-consed S-expressions for the engine. Every list is interned, so two
//! equal terms share one node: equality, hashing and ordering cost O(1), and
//! cloning copies a pointer. The engine is untrusted; this only changes how
//! fast it builds derivations, which print exactly as before.
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::rc::Rc;

pub use crate::sexp::Result;

#[derive(Clone)]
pub enum Sexp {
    Atom(Rc<str>),
    List(Items),
}

/// The children of an interned list; dereferences to a slice.
#[derive(Clone)]
pub struct Items(Rc<Node>);

pub struct Node {
    /// Interning order: deterministic, and unique per distinct list.
    id: u64,
    items: Box<[Sexp]>,
}

impl Deref for Items {
    type Target = [Sexp];
    fn deref(&self) -> &[Sexp] {
        &self.0.items
    }
}

impl PartialEq for Sexp {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Sexp::Atom(a), Sexp::Atom(b)) => a == b,
            (Sexp::List(a), Sexp::List(b)) => Rc::ptr_eq(&a.0, &b.0),
            _ => false,
        }
    }
}
impl Eq for Sexp {}

impl Hash for Sexp {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Sexp::Atom(a) => {
                0u8.hash(state);
                a.hash(state);
            }
            Sexp::List(xs) => {
                1u8.hash(state);
                xs.0.id.hash(state);
            }
        }
    }
}

impl Ord for Sexp {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (Sexp::Atom(a), Sexp::Atom(b)) => a.cmp(b),
            (Sexp::Atom(_), Sexp::List(_)) => std::cmp::Ordering::Less,
            (Sexp::List(_), Sexp::Atom(_)) => std::cmp::Ordering::Greater,
            (Sexp::List(a), Sexp::List(b)) => a.0.id.cmp(&b.0.id),
        }
    }
}
impl PartialOrd for Sexp {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// A fast, deterministic hasher for the engine's maps (the FxHash
/// multiply-rotate). Interned lists hash as their interning id, so keys are
/// short; SipHash's resistance to adversarial keys is not needed for an
/// untrusted producer whose output is checked anyway.
#[derive(Default, Clone, Copy)]
pub struct FastHasher(u64);

impl FastHasher {
    #[inline]
    fn add(&mut self, word: u64) {
        self.0 = (self.0.rotate_left(5) ^ word).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }
}

impl Hasher for FastHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let mut chunks = bytes.chunks_exact(8);
        for c in &mut chunks {
            self.add(u64::from_le_bytes(c.try_into().unwrap()));
        }
        let rest = chunks.remainder();
        if !rest.is_empty() {
            let mut word = [0u8; 8];
            word[..rest.len()].copy_from_slice(rest);
            self.add(u64::from_le_bytes(word));
        }
    }
    #[inline]
    fn write_u8(&mut self, i: u8) {
        self.add(u64::from(i));
    }
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.add(i);
    }
    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.add(i as u64);
    }
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }
}

pub type FastBuild = std::hash::BuildHasherDefault<FastHasher>;
/// A `HashMap` with the engine's fast hasher.
pub type FastMap<K, V> = HashMap<K, V, FastBuild>;
/// A `HashSet` with the engine's fast hasher.
pub type FastSet<K> = std::collections::HashSet<K, FastBuild>;

/// An interned list as a table key: it hashes and compares as its children,
/// so the table is probed with a borrowed slice and the node's own children
/// serve as the key (no second copy).
struct Key(Items);

impl Hash for Key {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.0.items.hash(state);
    }
}
impl PartialEq for Key {
    fn eq(&self, other: &Self) -> bool {
        self.0.0.items == other.0.0.items
    }
}
impl Eq for Key {}
impl std::borrow::Borrow<[Sexp]> for Key {
    fn borrow(&self) -> &[Sexp] {
        &self.0.0.items
    }
}

#[derive(Default)]
struct Interner {
    lists: std::collections::HashSet<Key, FastBuild>,
    atoms: FastMap<Box<str>, Rc<str>>,
    /// Atoms by the address and length of the text they were last requested
    /// with. Rule and constructor names are string literals, so this mostly
    /// avoids hashing their text; a hit is confirmed by comparing the text.
    recent: FastMap<(usize, usize), Rc<str>>,
    /// Children of the list being built, reused so a lookup that finds an
    /// existing list allocates nothing.
    scratch: Vec<Sexp>,
    /// Unary numerals `(s ... (s z))` by value.
    numerals: Vec<Sexp>,
}

/// The table lives as long as its thread unless `keep_terms_until_exit` was
/// called: then freeing millions of nodes is left to the operating system.
struct Table(std::mem::ManuallyDrop<RefCell<Interner>>);

impl Drop for Table {
    fn drop(&mut self) {
        if !KEEP_UNTIL_EXIT.load(std::sync::atomic::Ordering::Relaxed) {
            // SAFETY: dropped exactly once, here.
            unsafe { std::mem::ManuallyDrop::drop(&mut self.0) }
        }
    }
}

static KEEP_UNTIL_EXIT: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Do not free interned terms when a thread ends. For command-line runs that
/// exit right after, where the teardown is pure cost.
pub fn keep_terms_until_exit() {
    KEEP_UNTIL_EXIT.store(true, std::sync::atomic::Ordering::Relaxed);
}

thread_local! {
    static INTERNER: Table = Table(std::mem::ManuallyDrop::new(RefCell::new(Interner::default())));
}

fn interned(interner: &mut Interner, items: &[Sexp]) -> Sexp {
    if let Some(found) = interner.lists.get(items) {
        return Sexp::List(found.0.clone());
    }
    let id = interner.lists.len() as u64;
    let node = Items(Rc::new(Node {
        id,
        items: items.into(),
    }));
    interner.lists.insert(Key(node.clone()));
    Sexp::List(node)
}

/// The interned list with these children.
pub fn list(items: Vec<Sexp>) -> Sexp {
    INTERNER.with(|cell| interned(&mut cell.0.borrow_mut(), &items))
}

fn atom_in(interner: &mut Interner, s: &str) -> Sexp {
    let place = (s.as_ptr() as usize, s.len());
    if let Some(found) = interner.recent.get(&place)
        && **found == *s
    {
        return Sexp::Atom(found.clone());
    }
    let shared = match interner.atoms.get(s) {
        Some(found) => found.clone(),
        None => {
            let shared: Rc<str> = Rc::from(s);
            interner.atoms.insert(s.into(), shared.clone());
            shared
        }
    };
    interner.recent.insert(place, shared.clone());
    Sexp::Atom(shared)
}

pub fn atom(s: impl AsRef<str>) -> Sexp {
    INTERNER.with(|cell| atom_in(&mut cell.0.borrow_mut(), s.as_ref()))
}

pub fn call(name: &str, args: impl IntoIterator<Item = Sexp>) -> Sexp {
    // Arguments are built before the table is borrowed: building one may
    // intern other terms.
    let args = args.into_iter();
    INTERNER.with(|cell| {
        let mut guard = cell.0.borrow_mut();
        let interner = &mut *guard;
        let mut items = std::mem::take(&mut interner.scratch);
        items.clear();
        items.push(atom_in(interner, name));
        drop(guard);
        items.extend(args);
        let mut interner = cell.0.borrow_mut();
        let out = interned(&mut interner, &items);
        items.clear();
        interner.scratch = items;
        out
    })
}

/// The unary numeral `(s ... (s z))` for `n`.
pub fn numeral(n: usize) -> Sexp {
    INTERNER.with(|cell| {
        let mut interner = cell.0.borrow_mut();
        if interner.numerals.is_empty() {
            let z = atom_in(&mut interner, "z");
            interner.numerals.push(z);
        }
        while interner.numerals.len() <= n {
            let s = atom_in(&mut interner, "s");
            let previous = interner.numerals.last().unwrap().clone();
            let next = interned(&mut interner, &[s, previous]);
            interner.numerals.push(next);
        }
        interner.numerals[n].clone()
    })
}

impl FromIterator<Sexp> for Items {
    fn from_iter<I: IntoIterator<Item = Sexp>>(iter: I) -> Self {
        match list(iter.into_iter().collect()) {
            Sexp::List(items) => items,
            Sexp::Atom(_) => unreachable!(),
        }
    }
}

impl Sexp {
    pub fn atom(&self) -> Result<&str> {
        match self {
            Sexp::Atom(a) => Ok(a),
            Sexp::List(_) => Err(format!("expected atom, found {self}")),
        }
    }
    pub fn list(&self) -> Result<&[Sexp]> {
        match self {
            Sexp::List(xs) => Ok(xs),
            Sexp::Atom(_) => Err(format!("expected list, found {self}")),
        }
    }
    /// Convert from the parser's syntax tree.
    pub fn from_syntax(s: &crate::sexp::Sexp) -> Sexp {
        match s {
            crate::sexp::Sexp::Atom(a) => atom(a),
            crate::sexp::Sexp::List(xs) => list(xs.iter().map(Sexp::from_syntax).collect()),
        }
    }
}

pub fn parse(input: &str) -> Result<Vec<Sexp>> {
    Ok(crate::sexp::parse(input)?
        .iter()
        .map(Sexp::from_syntax)
        .collect())
}

impl fmt::Display for Sexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sexp::Atom(a) => f.write_str(a),
            Sexp::List(xs) => {
                f.write_str("(")?;
                for (i, x) in xs.iter().enumerate() {
                    if i > 0 {
                        f.write_str(" ")?;
                    }
                    write!(f, "{x}")?;
                }
                f.write_str(")")
            }
        }
    }
}

impl fmt::Debug for Sexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}
