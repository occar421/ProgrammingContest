#[cfg(test)]
mod tests {
    use templates::snippet_adjacent::adjacent::Adjacent2d;

    #[test]
    fn adjacent2d_free() {
        let dydx = vec![(-1, 0), (0, 1), (1, 0), (0, -1)];
        let ads = Adjacent2d::new((0, 0), 0..=1, 0..=1, dydx.iter());
        let ads: Vec<_> = ads.collect();
        assert_eq!(ads.len(), 2);
        assert_eq!(ads[0], (0, 1));
        assert_eq!(ads[1], (1, 0));

        let ads = Adjacent2d::new((1, 1), 0..=1, 0..=1, dydx.iter());
        let ads: Vec<_> = ads.collect();
        assert_eq!(ads.len(), 2);
        assert_eq!(ads[0], (0, 1));
        assert_eq!(ads[1], (1, 0));

        let ads = Adjacent2d::new((0, 1), 0..=0, 0..=2, dydx.iter());
        let ads: Vec<_> = ads.collect();
        assert_eq!(ads.len(), 2);
        assert_eq!(ads[0], (0, 2));
        assert_eq!(ads[1], (0, 0));
    }
}
