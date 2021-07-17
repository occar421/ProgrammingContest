pub mod golden_section_search {
    #[derive(Copy, Clone, Debug)]
    pub struct MaxResultFx {
        pub max_fx: f64,
        pub arg_max_fx: f64,
    }

    #[derive(Copy, Clone, Debug)]
    pub struct MinResultFx {
        pub min_fx: f64,
        pub arg_min_fx: f64,
    }

    pub trait GoldenSectionSearchFx {
        /// O( log(N) )
        /// `f` should be convex function and unimodal
        fn search_min(&self, lower_limit: f64, upper_limit: f64, error: f64) -> MinResultFx;

        /// O( log(N) )
        /// `f` should be convex function and unimodal
        fn search_max(&self, lower_limit: f64, upper_limit: f64, error: f64) -> MaxResultFx;
    }

    impl<F> GoldenSectionSearchFx for F
    where
        F: Fn(f64) -> f64,
    {
        fn search_min(&self, lower_limit: f64, upper_limit: f64, error: f64) -> MinResultFx {
            let phi = (1.0 + 5f64.sqrt()) / 2.0;
            let f = self;

            let mut low = lower_limit;
            let mut high = upper_limit;
            let mut lower = (low * phi + high) / (1.0 + phi);
            let mut higher = (low + high * phi) / (1.0 + phi);
            while high - low > error {
                if f(lower) < f(higher) {
                    high = higher;
                    higher = lower;
                    lower = (low * phi + high) / (1.0 + phi);
                } else {
                    low = lower;
                    lower = higher;
                    higher = (low + high * phi) / (1.0 + phi);
                }
            }

            let arg_min_fx = low;
            MinResultFx {
                min_fx: self(arg_min_fx),
                arg_min_fx,
            }
        }

        #[inline]
        fn search_max(&self, lower_limit: f64, upper_limit: f64, error: f64) -> MaxResultFx {
            let MinResultFx {
                arg_min_fx: arg_max_fx,
                ..
            } = (|x| -self(x)).search_min(lower_limit, upper_limit, error);

            MaxResultFx {
                max_fx: self(arg_max_fx),
                arg_max_fx,
            }
        }
    }
}
