//macro_rules! declare_test {
//    ($name:ident: $actual:expr => $expected:expr) => {
//        #[test]
//        fn $name() {
//            assert_eq!($actual, $expected);
//        }
//    }
//}
//
//macro_rules! table_tests {
//    ($target:path >>> [$($e1: expr, $e2: expr => $a: expr;)+]) => {
//        paste::item! {
//            $( declare_test!([<_ $e1 _ $e2>]: $target($e1, $e2) => $a); )+
//        }
//    };
//}

macro_rules! table_tests {
    ($target:path >>> [$($e1: expr, $e2: expr => $a: expr;)+]) => {
        paste::item! {
            $(
            #[test]
            fn [<_ $e1 _ $e2>]() {
                let expected = $target($e1, $e2);
                assert_eq!(expected, $a);
            }
            )+
        }
    };
}


#[cfg(test)]
mod tests {
    mod gcd_tests {
        use templates::standard_io::gcd;

        table_tests! { gcd >>> [
            1, 1 => 1;
            2, 1 => 1;
            1, 2 => 1;
            2, 2 => 2;
            6, 2 => 2;
            12, 8 => 4;
            3, 5 => 1;
        ]}
    }

    mod lcm_tests {
        use templates::standard_io::lcm;

        table_tests! { lcm >>> [
            1, 1 => 1;
            1, 2 => 2;
            2, 1 => 2;
            2, 2 => 2;
            6, 2 => 6;
            12, 8 => 24;
            3, 5 => 15;
        ]}
    }
}