#[cfg(test)]
mod tests {
    use templates::snippet_golden_section_search::golden_section_search::GoldenSectionSearchFx;

    #[test]
    fn x_2_min() {
        let f = |x: f64| x * x;
        let r = f.search_min(-10.0, 10.0, 10f64.powi(-9));
        assert!(r.arg_min_fx.abs() < 10f64.powi(-8));
        assert!(r.min_fx.abs() < 10f64.powi(-8));
    }

    #[test]
    fn neg_x_2_min() {
        let f = |x: f64| -x * x;
        let r = f.search_max(-10.0, 10.0, 10f64.powi(-9));
        assert!(r.arg_max_fx.abs() < 10f64.powi(-8));
        assert!(r.max_fx.abs() < 10f64.powi(-8));
    }

    #[test]
    fn _2x_min() {
        let f = |x: f64| 2.0 * x;
        let r = f.search_min(-10.0, 10.0, 10f64.powi(-9));

        assert!((-10.0 - r.arg_min_fx).abs() < 10f64.powi(-8));
        assert!((-20.0 - r.min_fx).abs() < 10f64.powi(-8));
    }

    fn cube_x(x: f64) -> f64 {
        // extremum: (-6, -6), (6, 6)
        // alpha = 6 sqrt(3)
        // beta = - 1 / (2 * 6^2)
        // f(x) = beta * (x^3 - alpha^2 * x);
        -(x * x * x - 108.0 * x) / 72.0
    }

    #[test]
    fn cube_x_min() {
        let r = cube_x.search_min(-10.0, 10.0, 10f64.powi(-9));

        assert!((-6.0 - r.arg_min_fx).abs() < 10f64.powi(-5));
        assert!((-6.0 - r.min_fx).abs() < 10f64.powi(-5));
    }

    #[test]
    fn cube_x_max() {
        let r = cube_x.search_max(-10.0, 10.0, 10f64.powi(-9));

        assert!((6.0 - r.arg_max_fx).abs() < 10f64.powi(-5));
        assert!((6.0 - r.max_fx).abs() < 10f64.powi(-5));
    }
}
