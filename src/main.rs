extern crate time;

fn main() {
    let solvers = [
        problem_001, problem_002, problem_003, problem_004, problem_005,
        problem_006, problem_007, problem_008, problem_009, problem_010];
    for s in &solvers {
        let now = time::now();
        s();
        let duration = time::now() - now;
        println!("{} elapsed.\n", duration);
    }
}

// Problem 1 - Project Euler <https://projecteuler.net/problem=1>
// Multiples of 3 and 5
fn problem_001() {
    println!("problem_001");
    let a = (1..1000)
        .filter(|e| e % 3 == 0 || e % 5 == 0)
        .fold(0, |acc, e| acc + e);
    println!("{:?}", &a);
}

struct Fib {
    a1: u64,
    a2: u64
}

impl Fib {
    fn new() -> Fib {
        Fib{a1: 1, a2: 2}
    }
}

impl Iterator for Fib {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        let a1 = self.a1;
        let a2 = self.a2;
        self.a1 = a2;
        self.a2 = a1 + a2;
        Some(a1)
    }
}

// Problem 2 - Project Euler <https://projecteuler.net/problem=2>
// Even Fibonacci numbers
fn problem_002() {
    println!("problem_002");
    let a = Fib::new();
    println!("{:?}", a.take_while(|&f| f < 4000000u64).fold(0, |acc, f| if f % 2 == 0 { acc + f } else { acc }));
}

fn prime_factors<'a>(n: u64, xs: &'a mut Vec<u64>) -> &'a Vec<u64> {
    for i in 2u64..(n as f64).sqrt() as u64 + 1 {
        if n % i == 0 {
            xs.push(i);
            return prime_factors(n / i, xs)
        }
    }
    xs.push(n);
    xs
}

// Problem 3 - Project Euler <https://projecteuler.net/problem=3>
// Largest prime factor
fn problem_003() {
    println!("problem_003");
    {
        let mut xs = vec![];
        let a = prime_factors(13195u64, &mut xs);
        println!("{:?}", a);
    }
    {
        let mut xs = vec![];
        let a = prime_factors(600851475143u64, &mut xs);
        println!("{:?}", a.iter().max().unwrap_or(&0u64));
    }
}

fn is_palindome(n: &u64) -> bool {
    let s = n.to_string();
    let t = n.to_string().chars().rev().collect::<String>();
    s == t
}

// Problem 4 - Project Euler <https://projecteuler.net/problem=4>
// Largest palindrome product
fn problem_004() {
    println!("problem_004");
    {
        let mut xs = vec![];
        let min = 10;
        let max = 100;
        for i in min..max {
            for j in i..max {
                let a = i * j;
                if is_palindome(&a) {
                    xs.push((i, j, a));
                }
            }
        }
        println!("{:?}", xs.iter().max_by_key(|n| n.2).unwrap_or(&(0, 0, 0)).2);
    }
    {
        let mut xs = vec![];
        let min = 100;
        let max = 1000;
        for i in min..max {
            for j in i..max {
                let a = i * j;
                if is_palindome(&a) {
                    xs.push((i, j, a));
                }
            }
        }
        println!("{:?}", xs.iter().max_by_key(|n| n.2).unwrap_or(&(0, 0, 0)).2);
    }
}

// Problem 5 - Project Euler <https://projecteuler.net/problem=5>
// Smallest multiple
fn problem_005() {
    println!("problem_005");
    {
        let max = 10u64;
        let a = (1u64..).find(|n| (2u64..max).all(|d| n % d == 0u64)).unwrap_or(0u64);
        println!("{}", a);
    }
    {
        let max = 20u64;
        let a = (1u64..).find(|n| (2u64..max).all(|d| n % d == 0u64)).unwrap_or(0u64);
        println!("{}", a);
    }
}

// Problem 6 - Project Euler <https://projecteuler.net/problem=6>
// Sum square difference
fn problem_006() {
    println!("problem_006");
    fn square(n: u64) -> u64 {
        n * n
    }
    {
        let max = 10u64;
        let sum_of_squares = (1..max + 1).fold(0, |acc, n| acc + square(n));
        let square_of_sum = square((1..max + 1).fold(0, |acc, n| acc + n));
        let a = square_of_sum - sum_of_squares;
        println!("{}", a);
    }
    {
        let max = 100u64;
        let sum_of_squares = (1..max + 1).fold(0, |acc, n| acc + square(n));
        let square_of_sum = square((1..max + 1).fold(0, |acc, n| acc + n));
        let a = square_of_sum - sum_of_squares;
        println!("{}", a);
    }
}

fn is_prime(n: &u64) -> bool {
    !(2u64..(*n as f64).sqrt() as u64 + 1).any(|x| n % x == 0)
}

// Problem 7 - Project Euler <https://projecteuler.net/problem=7>
// 10001st prime
fn problem_007() {
    println!("problem_007");
    {
        let n = 6;
        let a = (2u64..).filter(|&x| is_prime(&x)).skip(n - 1).nth(0).unwrap_or(0u64);
        println!("{:?}", a);
    }
    {
        let n = 10001;
        let a = (2u64..).filter(|&x| is_prime(&x)).skip(n - 1).nth(0).unwrap_or(0u64);
        println!("{:?}", a);
    }
}

fn problem_008() {
    println!("problem_008");
    let s = "73167176531330624919225119674426574742355349194934\
        96983520312774506326239578318016984801869478851843\
        85861560789112949495459501737958331952853208805511\
        12540698747158523863050715693290963295227443043557\
        66896648950445244523161731856403098711121722383113\
        62229893423380308135336276614282806444486645238749\
        30358907296290491560440772390713810515859307960866\
        70172427121883998797908792274921901699720888093776\
        65727333001053367881220235421809751254540594752243\
        52584907711670556013604839586446706324415722155397\
        53697817977846174064955149290862569321978468622482\
        83972241375657056057490261407972968652414535100474\
        82166370484403199890008895243450658541227588666881\
        16427171479924442928230863465674813919123162824586\
        17866458359124566529476545682848912883142607690042\
        24219022671055626321111109370544217506941658960408\
        07198403850962455444362981230987879927244284909188\
        84580156166097919133875499200524063689912560717606\
        05886116467109405077541002256983155200055935729725\
        71636269561882670428252483600823257530420752963450";
    {
        use std::cmp;

        let len = 4;
        let mut a = 0;
        for i in 0..s.len() - len + 1 {
            let ns = s[i..i + len].chars().map(|c| c.to_string().parse::<u64>().unwrap_or(0));
            let n = ns.fold(1, |acc, n| acc * n);
            a = cmp::max(a, n);
        }
        println!("{:?}", a);
    }
    {
        use std::cmp;

        let len = 13;
        let mut a = 0;
        for i in 0..s.len() - len + 1 {
            let ns = s[i..i + len].chars().map(|c| c.to_string().parse::<u64>().unwrap_or(0));
            let n = ns.fold(1, |acc, n| acc * n);
            a = cmp::max(a, n);
        }
        println!("{:?}", a);
    }
}

fn pythagorean_triplet(a: u64, b: u64, c: u64) -> Option<u64> {
    fn square(n: u64) -> u64 {
        n * n
    }
    let a2 = square(a);
    let b2 = square(b);
    let c2 = square(c);
    if a2 + b2 == c2 {
        Some(a * b * c)
    } else {
        None
    }
}

// Problem 9 - Project Euler <https://projecteuler.net/problem=9>
// Special Pythagorean triplet
fn problem_009() {
    println!("problem_009");
    {
        for a in 1..1000 {
            for b in a..1000 {
                for c in b..1000 {
                    if a + b + c == 1000 {
                        match pythagorean_triplet(a, b, c) {
                            Some(n) => println!("{} ** 2 * {} ** 2 = {} ** 2 -> {}", a, b, c, n),
                            None => ()
                        }
                    }
                }
            }
        }
    }
}

// Problem 10 - Project Euler <https://projecteuler.net/problem=10>
// Summation of primes
fn problem_010() {
    println!("problem_010");
    {
        let max = 10u64;
        let a = (2u64..max).filter(|n| is_prime(n)).fold(0, |acc, n| acc + n);
        println!("{}", a);
    }
    {
        let max = 2000000u64;
        let a = (2u64..max).filter(|n| is_prime(n)).fold(0, |acc, n| acc + n);
        println!("{}", a);
    }
}
