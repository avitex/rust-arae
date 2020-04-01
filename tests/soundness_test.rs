#[test]
fn test_soundness() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/soundness/*.rs");
}
