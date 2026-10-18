//! The engine moved from kamo3 regenerates bundled examples inside Horn.
//! Only the small ua-transport example runs here; canonicity and univalence
//! regenerate with `horn cubical generate NAME` (minutes, a few GB).
use horn::cubical;

#[test]
fn ua_transport_regenerates_to_the_bundled_goal_and_checks() {
    let example = cubical::EXAMPLES
        .iter()
        .find(|e| e.name == "ua-transport")
        .unwrap();
    let generated = cubical::generate::regenerate("ua-transport").unwrap();
    assert_eq!(generated.goals, example.goals);
    assert_eq!(generated.checked.goals, 1);
    assert!(cubical::generate::regenerate("missing").is_err());
}
