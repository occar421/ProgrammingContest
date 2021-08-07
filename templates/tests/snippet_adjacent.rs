#[cfg(test)]
mod tests {
    use templates::snippet_adjacent::adjacent::{
        adjacent2d_4neighbors, adjacent2d_8neighbors, Adjacent2d,
    };

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

    #[test]
    fn adjacent2d_4() {
        let ads = adjacent2d_4neighbors((1, 1), ..=2, ..=2);
        let ads: Vec<_> = ads.collect();
        assert_eq!(ads.len(), 4);
        assert_eq!(ads[0], (0, 1));
        assert_eq!(ads[1], (1, 2));
        assert_eq!(ads[2], (2, 1));
        assert_eq!(ads[3], (1, 0));
    }

    #[test]
    fn adjacent2d_8() {
        let ads = adjacent2d_8neighbors((1, 1), ..=2, ..=2);
        let ads: Vec<_> = ads.collect();
        assert_eq!(ads.len(), 8);
        assert_eq!(ads[0], (0, 1));
        assert_eq!(ads[1], (0, 2));
        assert_eq!(ads[2], (1, 2));
        assert_eq!(ads[3], (2, 2));
        assert_eq!(ads[4], (2, 1));
        assert_eq!(ads[5], (2, 0));
        assert_eq!(ads[6], (1, 0));
        assert_eq!(ads[7], (0, 0));
    }
}
