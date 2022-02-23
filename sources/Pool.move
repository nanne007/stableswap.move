

module Owner::Pool {
    use StarcoinFramework::Token;
    use StarcoinFramework::Timestamp;
    use StarcoinFramework::Math;
    use StarcoinFramework::Vector;
    const N_COINS: u64 = 3;

    const MIM_RAMP_TIME: u128 = 86400;
    // FIXME: check the value
    const MAX_A: u128 = 1000000; // 1e6
    const MAX_A_CHANGE: u128 = 10;

    const MAX_ADMIN_FEE: u128 = 10 * 1000 * 1000 * 1000; // 10 * 1e9
    const MAX_FEE: u128 = 5 * 1000 * 1000 * 1000; // 5 * 1e9




    struct PoolTokenT<phantom T1, phantom T2, phantom T3> has store {}

    struct PoolInfo<phantom T1, phantom T2, phantom T3> has key {
        initial_A: u128,
        future_A: u128,
        initial_A_time: u128,
        future_A_time: u128,
    }

    struct PoolConfig<phantom T1, phantom T2, phantom T3> has key {
        fee: u64,
        admin_fee: u64,

        lending_precision: u8,
        /// the precison to convert to
        precision: u8,
        precision_mul: vector<u128>,
        rates: vector<u128>,
    }

    struct Pool<phantom T1, phantom T2, phantom T3> has key {
        t1: Token::Token<T1>,
        t2: Token::Token<T2>,
        t3: Token::Token<T3>,
    }

    public fun initialize<T1, T2, T3>(sender: &signer, initial_A: u128,fee: u64,admin_fee: u64) {
        move_to(sender, PoolInfo<T1,T2,T3> {
            initial_A,
            future_A: initial_A,
            initial_A_time: 0u128,
            future_A_time: 0u128,
        });
        let precision = 9;
        let lending_precision = 9;
        let precision_mul = vector[
            Math::pow(10, precision) / Token::scaling_factor<T1>(),
            Math::pow(10, precision) / Token::scaling_factor<T2>(),
            Math::pow(10, precision) / Token::scaling_factor<T3>(),
        ];
        let rates = vector[
            Math::pow(10, precision) * Math::pow(10, lending_precision) / Token::scaling_factor<T1>(),
            Math::pow(10, precision) * Math::pow(10, lending_precision) / Token::scaling_factor<T2>(),
            Math::pow(10, precision) * Math::pow(10, lending_precision) / Token::scaling_factor<T3>(),
        ];

        move_to(sender, PoolConfig<T1,T2,T3> {
            fee,
            admin_fee,
            lending_precision: (lending_precision as u8),
            precision: (precision as u8),
            precision_mul,
            rates,

        });
    }

    public fun balances<T1, T2, T3>(): vector<u128> acquires Pool {
        balances_(borrow_global<Pool<T1, T2, T3>>(@Owner))
    }

    public fun add_liquidity<T1, T2, T3>(
        _t1: &mut Token::Token<T1>, _t2: &mut Token::Token<T2>, _t3: &mut Token::Token<T3>, _min_mint_amount: u128
    ) acquires PoolInfo, PoolConfig {
        let _fees: vector<u128> = vector[];
        let pool_info = borrow_global<PoolInfo<T1, T2, T3>>(@Owner);
        let pool_config = borrow_global<PoolConfig<T1, T2, T3>>(@Owner);
        let _fee = pool_config.fee * N_COINS / (4 * (N_COINS-1));
        let _admin_fee= pool_config.admin_fee;

        let _amp = A_(pool_info);

        let _total_supply = Token::market_cap<PoolTokenT<T1, T2, T3>>();
    }

    public fun A<T1, T2, T3>() : u128 acquires PoolInfo {
        let pool_info = borrow_global<PoolInfo<T1,T2,T3>>(@Owner);
        A_(pool_info)
    }


    fun balances_<T1, T2, T3>(pool: &Pool<T1, T2, T3>): vector<u128> {
        vector[
            Token::value(&pool.t1),
            Token::value(&pool.t2),
            Token::value(&pool.t3)
        ]
    }

    /// Handle ramping A up or down
    fun A_<T1, T2, T3>(pool_info: &PoolInfo<T1,T2,T3>): u128 {
        let t1 = pool_info.future_A_time;
        let _A1 = pool_info.future_A;

        let current_timestamp = (Timestamp::now_seconds() as u128);

        if (current_timestamp >= t1) {
            return _A1
        };

        let t0 = pool_info.initial_A_time;
        let _A0 = pool_info.initial_A;

        if (_A1 > _A0) {
            _A0 + (_A1 - _A0) * (current_timestamp - t0) / (t1 - t0)
        } else {
            _A0 - (_A0 - _A1) * (current_timestamp - t0) / (t1 - t0)
        }

    }



    fun xp_< T1, T2, T3>(config: &PoolConfig<T1,T2,T3>): vector<u128> acquires Pool {
        let lending_precision = (config.lending_precision as u64);
        let rates = *&config.rates;

        let balances = balances<T1,T2,T3>();

        {
            let i = 0;

            while (i < N_COINS) {
                let rate = Vector::borrow_mut(&mut rates, i);
                let bal = *Vector::borrow(&balances, i);
                *rate = *rate * bal / Math::pow(10, lending_precision);
                i=i+1;
            };
        };

        rates
    }

    fun xp_mem_(rates: vector<u128>, balances: vector<u128>, precision: u64): vector<u128> {
        {
            let i = 0;

            while (i < N_COINS) {
                let rate = Vector::borrow_mut(&mut rates, i);
                let bal = *Vector::borrow(&balances, i);
                *rate = *rate * bal / Math::pow(10, precision);
                i=i+1;
            };
        };

        rates
    }

    fun get_D_(xp: &vector<u128>, amp: u128): u128 {

        // sum of x_i
        let _S = 0u128;
        {
            let i = 0;
            while (i < Vector::length(xp)) {
                let x = *Vector::borrow(xp, i);
                _S = _S + x;
                i=i+1;
            };
            if (_S == 0) {
                return 0
            };
        };


        let _D = _S;
        {
            let _Ann = amp * (N_COINS as u128);
            let prev_D;
            let i = 0;
            while (i < 256) {
                // calculate D_P =  D**(n+1) / (n**n * x_1 * x_2 * x_3)
                let _D_P = _D;
                let j = 0;
                while (j < Vector::length(xp)) {
                    let x = *Vector::borrow(xp, i);
                    _D_P = _D_P * _D / (x * (N_COINS as u128));
                    j=i+1;
                };

                prev_D = _D;
                _D = (_Ann * _S + _D_P * (N_COINS as u128)) * _D / ((_Ann - 1) * _D + ((N_COINS as u128) + 1) * _D_P);

                if (_D > prev_D) {
                    if (_D - prev_D <= 1) {
                        break
                    }
                } else {
                    if (prev_D - _D <= 1) {
                        break
                    }
                };

                i=i+1;
            }
        };
        _D
    }

    /// Admin function
    fun ramp_A< T1, T2, T3>(pool_info: &mut PoolInfo<T1, T2, T3>, future_A: u128, future_A_time: u128) {
        let current_timestamp = (Timestamp::now_seconds() as u128);
        assert!(current_timestamp >= pool_info.initial_A_time + MIM_RAMP_TIME, 100);
        assert!(future_A_time >= current_timestamp + MIM_RAMP_TIME, 100);


        let initial_A = A_(pool_info);
        assert!(future_A > 0 && future_A < MAX_A, 200);
        assert!(
            (initial_A <= future_A && future_A <= initial_A * MAX_A_CHANGE) ||
            (initial_A <= future_A * MAX_A_CHANGE && future_A < initial_A),
            300
        );

        pool_info.initial_A = initial_A;
        pool_info.future_A = future_A;
        pool_info.initial_A_time = current_timestamp;
        pool_info.future_A_time = future_A_time;
    }

    /// admin function
    fun stop_ramp_A< T1, T2, T3>(pool_info: &mut PoolInfo<T1, T2, T3>) {
        let initial_A = A_(pool_info);

        pool_info.initial_A = initial_A;
        pool_info.future_A = initial_A;

        let current_timestamp = (Timestamp::now_seconds() as u128);
        pool_info.initial_A_time = current_timestamp;
        pool_info.future_A_time = current_timestamp;
        // now (block.timestamp < t1) is always false, so we return saved A
    }
}