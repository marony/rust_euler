fn main() {
    extern crate time;

    let solvers = [
        /*problem_001, problem_002, problem_003, problem_004, problem_005,
        problem_006, problem_007, problem_008, problem_009, problem_010,
        problem_011, problem_012, problem_013, */problem_014];
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

fn problem_011() {
    println!("problem_011");
    const LEN: usize = 4;
    const SLEN: i32 = 20;
    let ss;
    {
        let s = "08 02 22 97 38 15 00 40 00 75 04 05 07 78 52 12 50 77 91 08 \
            49 49 99 40 17 81 18 57 60 87 17 40 98 43 69 48 04 56 62 00 \
            81 49 31 73 55 79 14 29 93 71 40 67 53 88 30 03 49 13 36 65 \
            52 70 95 23 04 60 11 42 69 24 68 56 01 32 56 71 37 02 36 91 \
            22 31 16 71 51 67 63 89 41 92 36 54 22 40 40 28 66 33 13 80 \
            24 47 32 60 99 03 45 02 44 75 33 53 78 36 84 20 35 17 12 50 \
            32 98 81 28 64 23 67 10 26 38 40 67 59 54 70 66 18 38 64 70 \
            67 26 20 68 02 62 12 20 95 63 94 39 63 08 40 91 66 49 94 21 \
            24 55 58 05 66 73 99 26 97 17 78 78 96 83 14 88 34 89 63 72 \
            21 36 23 09 75 00 76 44 20 45 35 14 00 61 33 97 34 31 33 95 \
            78 17 53 28 22 75 31 67 15 94 03 80 04 62 16 14 09 53 56 92 \
            16 39 05 42 96 35 31 47 55 58 88 24 00 17 54 24 36 29 85 57 \
            86 56 00 48 35 71 89 07 05 44 44 37 44 60 21 58 51 54 17 58 \
            19 80 81 68 05 94 47 69 28 73 92 13 86 52 17 77 04 89 55 40 \
            04 52 08 83 97 35 99 16 07 97 57 32 16 26 26 79 33 27 98 66 \
            88 36 68 87 57 62 20 72 03 46 33 67 46 55 12 32 63 93 53 69 \
            04 42 16 73 38 25 39 11 24 94 72 18 08 46 29 32 40 62 76 36 \
            20 69 36 41 72 30 23 88 34 62 99 69 82 67 59 85 74 04 36 16 \
            20 73 35 29 78 31 90 01 74 31 49 71 48 86 81 16 23 57 05 54 \
            01 70 54 71 83 51 54 69 16 92 33 48 61 43 52 01 89 19 67 48";
        ss = s.split_whitespace().map(|s| s.parse::<i32>().unwrap_or(0i32)).collect::<Vec<_>>();
    }
    fn get_nums<'a>(ss: &'a Vec<i32>, index: i32) -> Vec<Vec<i32>> {
        let mut nss: Vec<Vec<i32>> = vec![];
        let x = (index % SLEN) as usize;
        let y = (index / SLEN) as usize;

        // 右
        let is = vec![(index + 0) as usize, (index + 1) as usize, (index + 2) as usize, (index + 3) as usize];
        if is.iter().all(|&i| 0 <= i && i < (SLEN * SLEN) as usize && (i / SLEN as usize) == y) {
            let mut ns = Vec::with_capacity(LEN);
            for i in 0..LEN {
                ns.push(ss[is[i]]);
            }
            nss.push(ns);
        } else {
            ()
        }
        // 下
        let is = vec![(index + 0) as usize, (index + SLEN) as usize, (index + SLEN * 2) as usize, (index + SLEN * 3) as usize];
        if is.iter().all(|&i| 0 <= i && i < (SLEN * SLEN) as usize && (i % SLEN as usize) == x) {
            let mut ns = Vec::with_capacity(LEN);
            for i in 0..LEN {
                ns.push(ss[is[i]]);
            }
            nss.push(ns);
        } else {
            ()
        }
        // 右下
        let is = vec![(index + 0) as usize, (index + SLEN + 1) as usize, (index + SLEN * 2 + 2) as usize, (index + SLEN * 3 + 3) as usize];
        if is.iter().all(|&i| 0 <= i && i < (SLEN * SLEN) as usize && (i % SLEN as usize) >= x && (i / SLEN as usize) >= y) {
            let mut ns = Vec::with_capacity(LEN);
            for i in 0..LEN {
                ns.push(ss[is[i]]);
            }
            nss.push(ns);
        } else {
            ()
        }
        // 左下
        let is = vec![(index + 0) as usize, (index + SLEN - 1) as usize, (index + SLEN * 2 - 2) as usize, (index + SLEN * 3 - 3) as usize];
        if is.iter().all(|&i| 0 <= i && i < (SLEN * SLEN) as usize && (i % SLEN as usize) <= x && (i / SLEN as usize) >= y) {
            let mut ns = Vec::with_capacity(LEN);
            for i in 0..LEN {
                ns.push(ss[is[i]]);
            }
            nss.push(ns);
        } else {
            ()
        }
        nss
    }
    {
        use std::cmp;

        let mut a = 0;
        for i in 0..SLEN * SLEN {
            for ns in get_nums(&ss, i) {
                a = cmp::max(a, ns.iter().fold(1, |acc, &n| acc * n));
            }
        }
        println!("{}", a);
    }
}

fn factors<'a>(n: u64) -> Vec<u64> {
    let mut xs = vec![];
    for i in 1u64..(n as f64).sqrt() as u64 + 1 {
        if n % i == 0 {
            xs.push(i);
            xs.push(n / i);
        }
    }
    xs
}

fn triangle_number(n: u64) -> u64 {
    (1 + n) * n / 2
}

// Problem 12 - Project Euler <https://projecteuler.net/problem=12>
// Highly divisible triangular number
fn problem_012<'a>() {
    println!("problem_012");
    {
        let x = 500;
        let a = (1..).map(|n| {
            let tri = triangle_number(n);
            let fac = factors(tri);
            let len = fac.len();
            (tri, fac, len)
        }).find(|xs| xs.2 > x).unwrap_or((0, vec![], 0));
        println!("{:?}", &a);
    }
}

fn problem_013() {
    println!("problem_013");
    const LEN: usize = 14;
    let lines;
    {
        let s = "37107287533902102798797998220837590246510135740250\n\
        46376937677490009712648124896970078050417018260538\n\
        74324986199524741059474233309513058123726617309629\n\
        91942213363574161572522430563301811072406154908250\n\
        23067588207539346171171980310421047513778063246676\n\
        89261670696623633820136378418383684178734361726757\n\
        28112879812849979408065481931592621691275889832738\n\
        44274228917432520321923589422876796487670272189318\n\
        47451445736001306439091167216856844588711603153276\n\
        70386486105843025439939619828917593665686757934951\n\
        62176457141856560629502157223196586755079324193331\n\
        64906352462741904929101432445813822663347944758178\n\
        92575867718337217661963751590579239728245598838407\n\
        58203565325359399008402633568948830189458628227828\n\
        80181199384826282014278194139940567587151170094390\n\
        35398664372827112653829987240784473053190104293586\n\
        86515506006295864861532075273371959191420517255829\n\
        71693888707715466499115593487603532921714970056938\n\
        54370070576826684624621495650076471787294438377604\n\
        53282654108756828443191190634694037855217779295145\n\
        36123272525000296071075082563815656710885258350721\n\
        45876576172410976447339110607218265236877223636045\n\
        17423706905851860660448207621209813287860733969412\n\
        81142660418086830619328460811191061556940512689692\n\
        51934325451728388641918047049293215058642563049483\n\
        62467221648435076201727918039944693004732956340691\n\
        15732444386908125794514089057706229429197107928209\n\
        55037687525678773091862540744969844508330393682126\n\
        18336384825330154686196124348767681297534375946515\n\
        80386287592878490201521685554828717201219257766954\n\
        78182833757993103614740356856449095527097864797581\n\
        16726320100436897842553539920931837441497806860984\n\
        48403098129077791799088218795327364475675590848030\n\
        87086987551392711854517078544161852424320693150332\n\
        59959406895756536782107074926966537676326235447210\n\
        69793950679652694742597709739166693763042633987085\n\
        41052684708299085211399427365734116182760315001271\n\
        65378607361501080857009149939512557028198746004375\n\
        35829035317434717326932123578154982629742552737307\n\
        94953759765105305946966067683156574377167401875275\n\
        88902802571733229619176668713819931811048770190271\n\
        25267680276078003013678680992525463401061632866526\n\
        36270218540497705585629946580636237993140746255962\n\
        24074486908231174977792365466257246923322810917141\n\
        91430288197103288597806669760892938638285025333403\n\
        34413065578016127815921815005561868836468420090470\n\
        23053081172816430487623791969842487255036638784583\n\
        11487696932154902810424020138335124462181441773470\n\
        63783299490636259666498587618221225225512486764533\n\
        67720186971698544312419572409913959008952310058822\n\
        95548255300263520781532296796249481641953868218774\n\
        76085327132285723110424803456124867697064507995236\n\
        37774242535411291684276865538926205024910326572967\n\
        23701913275725675285653248258265463092207058596522\n\
        29798860272258331913126375147341994889534765745501\n\
        18495701454879288984856827726077713721403798879715\n\
        38298203783031473527721580348144513491373226651381\n\
        34829543829199918180278916522431027392251122869539\n\
        40957953066405232632538044100059654939159879593635\n\
        29746152185502371307642255121183693803580388584903\n\
        41698116222072977186158236678424689157993532961922\n\
        62467957194401269043877107275048102390895523597457\n\
        23189706772547915061505504953922979530901129967519\n\
        86188088225875314529584099251203829009407770775672\n\
        11306739708304724483816533873502340845647058077308\n\
        82959174767140363198008187129011875491310547126581\n\
        97623331044818386269515456334926366572897563400500\n\
        42846280183517070527831839425882145521227251250327\n\
        55121603546981200581762165212827652751691296897789\n\
        32238195734329339946437501907836945765883352399886\n\
        75506164965184775180738168837861091527357929701337\n\
        62177842752192623401942399639168044983993173312731\n\
        32924185707147349566916674687634660915035914677504\n\
        99518671430235219628894890102423325116913619626622\n\
        73267460800591547471830798392868535206946944540724\n\
        76841822524674417161514036427982273348055556214818\n\
        97142617910342598647204516893989422179826088076852\n\
        87783646182799346313767754307809363333018982642090\n\
        10848802521674670883215120185883543223812876952786\n\
        71329612474782464538636993009049310363619763878039\n\
        62184073572399794223406235393808339651327408011116\n\
        66627891981488087797941876876144230030984490851411\n\
        60661826293682836764744779239180335110989069790714\n\
        85786944089552990653640447425576083659976645795096\n\
        66024396409905389607120198219976047599490197230297\n\
        64913982680032973156037120041377903785566085089252\n\
        16730939319872750275468906903707539413042652315011\n\
        94809377245048795150954100921645863754710598436791\n\
        78639167021187492431995700641917969777599028300699\n\
        15368713711936614952811305876380278410754449733078\n\
        40789923115535562561142322423255033685442488917353\n\
        44889911501440648020369068063960672322193204149535\n\
        41503128880339536053299340368006977710650566631954\n\
        81234880673210146739058568557934581403627822703280\n\
        82616570773948327592232845941706525094512325230608\n\
        22918802058777319719839450180888072429661980811197\n\
        77158542502016545090413245809786882778948721859617\n\
        72107838435069186155435662884062257473692284509516\n\
        20849603980134001723930671666823555245252804609722\n\
        53503534226472524250874054075591789781264330331690";
        lines = s.lines().map(|l| l[0..LEN].parse::<u64>().unwrap_or(0u64));
    }

    {
        let a = lines.fold(0, |acc, n| acc + n).to_string();
        println!("{:?}", &a[0..10]);
    }
}

fn problem_014() {
    println!("problem_014");
    fn is_even(n: u64) -> bool {
        n % 2 == 0
    }
    fn collatz(n: u64, m: i32) -> i32
    {
        if n == 1 {
            return m + 1;
        }
        if is_even(n) {
            collatz(n / 2, m + 1)
        } else {
            collatz(n * 3 + 1, m + 1)
        }
    }
    {
        let max = 1000000u64;
        let a = (1u64..max).map(|n| (n, collatz(n, 0))).max_by_key(|t| t.1).unwrap_or((0, 0));
        println!("{:?}", a);
    }
}
