#[cfg(test)]
mod tests {
    use templates::snippet_adjacent::adjacent::{
        adjacent2d_4neighbors, adjacent2d_8neighbors, Adjacent2d,
    };
    use templates::standard_io::Point2d;

    #[test]
    fn adjacent2d_free() {
        let dydx = vec![
            Point2d { x: 0, y: -1 },
            Point2d { x: 1, y: 0 },
            Point2d { x: 0, y: 1 },
            Point2d { x: -1, y: 0 },
        ];
        let ads = Adjacent2d::new(Point2d { x: 0, y: 0 }, 0..=1, 0..=1, dydx.iter());
        let ads: Vec<_> = ads.collect();
        assert_eq!(ads.len(), 2);
        assert_eq!(ads[0], Point2d { x: 1, y: 0 });
        assert_eq!(ads[1], Point2d { x: 0, y: 1 });

        let ads = Adjacent2d::new(Point2d { x: 1, y: 1 }, 0..=1, 0..=1, dydx.iter());
        let ads: Vec<_> = ads.collect();
        assert_eq!(ads.len(), 2);
        assert_eq!(ads[0], Point2d { x: 1, y: 0 });
        assert_eq!(ads[1], Point2d { x: 0, y: 1 });

        let ads = Adjacent2d::new(Point2d { x: 1, y: 0 }, 0..=0, 0..=2, dydx.iter());
        let ads: Vec<_> = ads.collect();
        assert_eq!(ads.len(), 2);
        assert_eq!(ads[0], Point2d { x: 2, y: 0 });
        assert_eq!(ads[1], Point2d { x: 0, y: 0 });
    }

    #[test]
    fn adjacent2d_4() {
        let ads = adjacent2d_4neighbors(Point2d { x: 1, y: 1 }, ..=2, ..=2);
        let ads: Vec<_> = ads.collect();
        assert_eq!(ads.len(), 4);
        assert_eq!(ads[0], Point2d { x: 1, y: 0 });
        assert_eq!(ads[1], Point2d { x: 2, y: 1 });
        assert_eq!(ads[2], Point2d { x: 1, y: 2 });
        assert_eq!(ads[3], Point2d { x: 0, y: 1 });
    }

    #[test]
    fn adjacent2d_8() {
        let ads = adjacent2d_8neighbors(Point2d { x: 1, y: 1 }, ..=2, ..=2);
        let ads: Vec<_> = ads.collect();
        assert_eq!(ads.len(), 8);
        assert_eq!(ads[0], Point2d { x: 1, y: 0 });
        assert_eq!(ads[1], Point2d { x: 2, y: 0 });
        assert_eq!(ads[2], Point2d { x: 2, y: 1 });
        assert_eq!(ads[3], Point2d { x: 2, y: 2 });
        assert_eq!(ads[4], Point2d { x: 1, y: 2 });
        assert_eq!(ads[5], Point2d { x: 0, y: 2 });
        assert_eq!(ads[6], Point2d { x: 0, y: 1 });
        assert_eq!(ads[7], Point2d { x: 0, y: 0 });
    }
}
