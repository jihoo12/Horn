//! The engine moved from kamo3 regenerates bundled examples inside Horn.
use horn::cubical;

#[test]
fn every_bundled_example_regenerates_to_its_goals_and_checks() {
    for example in cubical::EXAMPLES {
        let generated = cubical::generate::regenerate(example.name).unwrap();
        assert_eq!(generated.goals, example.goals, "{}", example.name);
        assert_eq!(generated.checked.goals, example.goals.lines().count());
    }
    assert!(cubical::generate::regenerate("missing").is_err());
}
