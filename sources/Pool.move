

module Owner::Pool {
    use StarcoinFramework::Token;
    use StarcoinFramework::Timestamp;
    use StarcoinFramework::Math;
    use StarcoinFramework::Vector;
    use Owner::Math as Math2;
    const N_COINS: u64 = 3;

    const MIM_RAMP_TIME: u128 = 86400;
    // FIXME: check the value
    const MAX_A: u128 = 1000000; // 1e6
    const MAX_A_CHANGE: u128 = 10;

    const MAX_ADMIN_FEE: u128 = 10 * 1000 * 1000 * 1000; // 10 * 1e9
    const MAX_FEE: u128 = 5 * 1000 * 1000 * 1000; // 5 * 1e9
    const FEE_DENOMINATOR: u128 = 10 * 1000 * 1000 * 1000; // 1e10



    struct PoolTokenT<phantom T1, phantom T2, phantom T3> has store {}

    struct PoolInfo<phantom T1, phantom T2, phantom T3> has key {
        store: PoolInfoStore,
    }
    struct PoolInfoStore has store {
        initial_A: u128,
        future_A: u128,
        initial_A_time: u128,
        future_A_time: u128,
        balances: vector<u128>,
    }

    struct PoolConfig<phantom T1, phantom T2, phantom T3> has key {
        store: PoolConfigStore,
    }

    struct PoolConfigStore has store {
        fee: u128,
        admin_fee: u128,

        lending_precision: u128,
        /// the precison to convert to
        precision: u128,
        precision_mul: vector<u128>,
        rates: vector<u128>,
    }

    struct PoolCapabilities<phantom T1, phantom T2, phantom T3> has key {
        mint_cap: Token::MintCapability<PoolTokenT<T1,T2,T3>>,
        burn_cap: Token::BurnCapability<PoolTokenT<T1,T2,T3>>,
    }

    struct Pool<phantom T1, phantom T2, phantom T3> has key {
        t1: Token::Token<T1>,
        t2: Token::Token<T2>,
        t3: Token::Token<T3>,
    }

    public fun initialize<T1, T2, T3>(sender: &signer, initial_A: u128,fee: u128,admin_fee: u128) {
        move_to(sender, PoolInfo<T1,T2,T3> {
            store: PoolInfoStore{
                initial_A,
                future_A: initial_A,
                initial_A_time: 0u128,
                future_A_time: 0u128,
                balances: vector[0u128, 0u128, 0u128],
            }
        });
        let precision = Math::pow(10, 9);
        let lending_precision = Math::pow(10, 9);
        let precision_mul = vector[
        precision / Token::scaling_factor<T1>(),
        precision / Token::scaling_factor<T2>(),
        precision / Token::scaling_factor<T3>(),
        ];
        let rates = vector[
            precision * lending_precision / Token::scaling_factor<T1>(),
            precision * lending_precision / Token::scaling_factor<T2>(),
            precision * lending_precision / Token::scaling_factor<T3>(),
        ];

        move_to(sender, PoolConfig<T1,T2,T3> {
            store: PoolConfigStore{
                fee,
                admin_fee,
                lending_precision,
                precision,
                precision_mul,
                rates,
            }
        });

        {
            Token::register_token<PoolTokenT<T1,T2,T3>>(sender, 9u8);
            let mint_cap = Token::remove_mint_capability<PoolTokenT<T1,T2,T3>>(sender);
            let burn_cap = Token::remove_burn_capability<PoolTokenT<T1,T2,T3>>(sender);
            move_to(sender, PoolCapabilities {
                mint_cap, burn_cap
            });
        }
    }

    public fun balances<T1, T2, T3>(): vector<u128> acquires PoolInfo {
        *&borrow_global<PoolInfo<T1, T2, T3>>(@Owner).store.balances
    }

    public fun add_liquidity<T1, T2, T3>(
        _t1: Token::Token<T1>, _t2:  Token::Token<T2>, _t3: Token::Token<T3>, _min_mint_amount: u128
    ): Token::Token<PoolTokenT<T1,T2,T3>> acquires PoolInfo, PoolConfig, PoolCapabilities, Pool {
        let pool_info = borrow_global_mut<PoolInfo<T1, T2, T3>>(@Owner);
        let pool_config = borrow_global<PoolConfig<T1, T2, T3>>(@Owner);

        let amounts = vector[Token::value(&_t1), Token::value(&_t2), Token::value(&_t3)];
        let total_supply = Token::market_cap<PoolTokenT<T1, T2, T3>>();

        let (new_balances, mint_amount) = add_liquidity_(&pool_config.store, &pool_info.store, &amounts, _min_mint_amount, total_supply);
        pool_info.store.balances = new_balances;


        let pool = borrow_global_mut<Pool<T1, T2, T3>>(@Owner);
        Token::deposit(&mut pool.t1, _t1);
        Token::deposit(&mut pool.t2, _t2);
        Token::deposit(&mut pool.t3, _t3);
        let pool_caps = borrow_global<PoolCapabilities<T1,T2,T3>>(@Owner);
        let lp_token = Token::mint_with_capability<PoolTokenT<T1,T2,T3>>(&pool_caps.mint_cap, mint_amount);
        lp_token
    }


    fun add_liquidity_(pool_config: &PoolConfigStore, pool_info: &PoolInfoStore,  amounts: &vector<u128>, min_mint_amount: u128, total_supply: u128): (vector<u128>, u128) {
        let n_coins = (N_COINS as u64);
        let fee = pool_config.fee * (n_coins as u128) / (4 * ((n_coins as u128)-1));
        let fee = (fee as u128);
        let admin_fee= (pool_config.admin_fee as u128);

        let amp = A_(pool_info);

        // Initial invariant
        let _D0 = 0u128;
        let old_balances = *&pool_info.balances;
        if (total_supply > 0) {
            _D0 = get_D_mem_(pool_config, &old_balances, amp);
        };
        let new_balances = (copy old_balances);

            {
                let i = 0;
                while (i < n_coins) {
                    let in_amount = *Vector::borrow(amounts, i);
                    if (total_supply == 0) {
                        // dev: initial deposit requries all coins
                        assert!(in_amount > 0, 400);
                    };

                    let new_balance = Vector::borrow_mut(&mut new_balances, i);
                    *new_balance = *new_balance + in_amount;
                };
            };


        // Invariant after change
        let _D1 = get_D_mem_(pool_config,&new_balances, amp);
        assert!(_D1 > _D0, 42);

        // we need to recalculate the invariant accounting for fees
        // to calculate fair user's share
        let _D2 = _D1;

        let new_balances_for_store = copy new_balances;
        if (total_supply>0) {
            let i = 0;
            while (i < n_coins) {
                let old_balance = *Vector::borrow(&old_balances, i);
                let new_balance_ref = Vector::borrow_mut(&mut new_balances, i);

                let ideal_balance = _D1 * old_balance / _D0;
                let difference;
                if (ideal_balance > *new_balance_ref) {
                    difference = ideal_balance - (*new_balance_ref);
                } else {
                    difference = (*new_balance_ref) - ideal_balance;
                };
                let the_fee = fee * difference / FEE_DENOMINATOR;
                *Vector::borrow_mut(&mut new_balances_for_store, i) = *new_balance_ref - (the_fee * admin_fee / FEE_DENOMINATOR);
                *new_balance_ref = *new_balance_ref - the_fee;
                i=i+1;
            };
            _D2 = get_D_mem_(pool_config, &new_balances, amp);
        };

        let mint_amount = 0u128;
        if (total_supply ==0) {
            mint_amount = _D1;
        } else {
            mint_amount == total_supply * (_D2 - _D0) / _D0;
        };
        assert!(mint_amount >= min_mint_amount, 100);
        (new_balances_for_store, mint_amount)
    }

    public fun remove_liquidity<T1, T2, T3>(lp_token: Token::Token<PoolTokenT<T1,T2,T3>>, min_amounts: &vector<u128>): (Token::Token<T1>,Token::Token<T2>,Token::Token<T3>)
    acquires  PoolInfo, Pool, PoolCapabilities {
        let pool_info = &mut borrow_global_mut<PoolInfo<T1, T2, T3>>(@Owner).store;
        //let pool_config = borrow_global<PoolConfig<T1, T2, T3>>(@Owner);
        let total_supply = Token::market_cap<PoolTokenT<T1,T2,T3>>();
        let amounts_to_withdraw = remove_liquidity_(pool_info, Token::value(&lp_token), total_supply, min_amounts);
        // update balances fields
            {
                let i = 0;
                while (i < N_COINS) {
                    let bal = Vector::borrow_mut(&mut pool_info.balances, i);
                    let amount_withdraw = *Vector::borrow(&amounts_to_withdraw, i);
                    *bal = (*bal) - amount_withdraw;
                    i = i + 1;
                };
            };
        // do asset handling
            {
                // burn lp token
                let pool_caps = borrow_global<PoolCapabilities<T1,T2,T3>>(@Owner);
                Token::burn_with_capability(&pool_caps.burn_cap, lp_token);

                // with underlying assets
                let pool = borrow_global_mut<Pool<T1,T2,T3>>(@Owner);
                let t1 = Token::withdraw(&mut pool.t1, *Vector::borrow(&amounts_to_withdraw, 0));
                let t2 = Token::withdraw(&mut pool.t2, *Vector::borrow(&amounts_to_withdraw, 1));
                let t3 = Token::withdraw(&mut pool.t3, *Vector::borrow(&amounts_to_withdraw, 2));
                (t1,t2,t3)
            }
    }
    fun remove_liquidity_(pool_info: &PoolInfoStore, lp_amount: u128, total_supply: u128, min_amounts: &vector<u128>): vector<u128> {
        let amounts_to_withdraw: vector<u128> = vector[];
        let current_balances = &pool_info.balances;
        let i = 0;
        while (i < N_COINS) {
            let balance = *Vector::borrow(current_balances, i);
            let amount_to_withdraw = lp_amount * balance / total_supply;
            assert!( amount_to_withdraw >= *Vector::borrow(min_amounts, i), 400);
            Vector::push_back(&mut amounts_to_withdraw, amount_to_withdraw);
            i = i + 1;
        };
        amounts_to_withdraw
    }

    public fun exchange_t1_for_t2<T1,T2,T3>(t1: Token::Token<T1>, min_dy: u128): Token::Token<T2> acquires  Pool, PoolInfo, PoolConfig {
        let pool_info = &mut borrow_global_mut<PoolInfo<T1,T2,T3>>(@Owner).store;
        let pool_config = &borrow_global<PoolConfig<T1,T2,T3>>(@Owner).store;
        let (new_balances, dy) = exchange_(pool_config, pool_info, 1, 2, Token::value(&t1), min_dy);

        // update pool balance
        pool_info.balances = new_balances;
        // do asset transfer.
            {

                let pool = borrow_global_mut<Pool<T1,T2,T3>>(@Owner);
                Token::deposit(&mut pool.t1, t1);
                let dy = Token::withdraw(&mut pool.t2, dy);
                dy
            }
    }

    /// returns:
    /// 1. `vector<u128>`: new_balances of the pool
    /// 2. `u128`: dy
    /// This function is a view function, it only does calculation.
    fun exchange_(pool_config: &PoolConfigStore, pool_info: &PoolInfoStore, i: u64, j: u64, dx: u128, min_dy: u128): (vector<u128>, u128) {
        let rates = &pool_config.rates;

        let old_balances = &pool_info.balances;
        let xp = xp_mem_(pool_config, old_balances);

        let x = *Vector::borrow(&xp, i) + dx * (*Vector::borrow(rates, i)) / pool_config.precision;
        let y = get_y(pool_info, i ,j , x, &xp);
        let dy = *Vector::borrow(&xp, j) - y - 1; // -1 just in case there were some rounding errors.
        let dy_fee = dy * pool_config.fee / FEE_DENOMINATOR;

        // convert all to real units
        let dy = (dy - dy_fee) * pool_config.precision / (*Vector::borrow(rates, j));
        assert!( dy >= min_dy, 400);

        let dy_admin_fee = dy_fee * pool_config.admin_fee / FEE_DENOMINATOR;
        let dy_admin_fee = dy_admin_fee * pool_config.precision / (*Vector::borrow(rates, j));

        let new_balances = *old_balances;
        *Vector::borrow_mut(&mut new_balances, i) = (*Vector::borrow(&new_balances, i)) + dx;
        *Vector::borrow_mut(&mut new_balances, j) = (*Vector::borrow(&new_balances, j)) - (dy + dy_admin_fee);

        (new_balances, dy)
    }

    public fun A<T1, T2, T3>() : u128 acquires PoolInfo {
        let pool_info = &borrow_global<PoolInfo<T1,T2,T3>>(@Owner).store;
        A_(pool_info)
    }


    fun get_y(pool_info: &PoolInfoStore, i: u64, j: u64, x: u128, xp: &vector<u128>): u128 {
        let n_coins = Vector::length(xp);


        let amp = A_(pool_info);
        let _D = get_D_(xp, amp);

        let _Ann = amp * (n_coins as u128);

        let c = _D;
        let _S = 0u128;

            {
                let _x = 0u128;
                let _i = 0;
                while (_i < n_coins) {
                    if (_i == i) {
                        _x = x;
                    } else if (_i != j) {
                        _x = *Vector::borrow(xp,i);
                    } else {
                        continue
                    };
                    _S = _S + _x;
                    c = c * _D / (_x * (n_coins as u128));
                };
                c = c * _D / (_Ann * (n_coins as u128));
            };
        let b = _S + _D / _Ann;

        // calculate y iteratly.
            {
                let y_prev;
                let y = _D;
                let _i = 0;
                while (_i < 256) {
                    y_prev = y;
                    y = (y * y +c) / (2 * y + b - _D);
                    if (Math2::diff(y, y_prev) <= 1) {
                        break
                    }
                };
                y
            }
    }

    /// Handle ramping A up or down
    fun A_(pool_info: &PoolInfoStore): u128 {
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



    fun xp_(config: &PoolConfigStore, balances: &vector<u128>): vector<u128> {
        let lending_precision = config.lending_precision;
        let rates = *&config.rates;

        {
            let i = 0;

            while (i < N_COINS) {
                let rate = Vector::borrow_mut(&mut rates, i);
                let bal = *Vector::borrow(balances, i);
                *rate = *rate * bal / lending_precision;
                i=i+1;
            };
        };

        rates
    }

    fun xp_mem_(pool_config: &PoolConfigStore, balances: &vector<u128>): vector<u128> {
        let rates = *&pool_config.rates;
        let precision = pool_config.precision;
        {
            let i = 0;

            while (i < N_COINS) {
                let rate = Vector::borrow_mut(&mut rates, i);
                let bal = *Vector::borrow(balances, i);
                *rate = *rate * bal / precision;
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

    fun get_D_mem_(pool_config: &PoolConfigStore, balances: &vector<u128>, amp: u128): u128 {
        get_D_(&xp_mem_(pool_config, balances), amp)
    }

    /// Admin function
    fun ramp_A< T1, T2, T3>(pool_info: &mut PoolInfo<T1, T2, T3>, future_A: u128, future_A_time: u128) {
        let pool_info = &mut pool_info.store;
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
        let pool_info = &mut pool_info.store;
        let initial_A = A_(pool_info);

        pool_info.initial_A = initial_A;
        pool_info.future_A = initial_A;

        let current_timestamp = (Timestamp::now_seconds() as u128);
        pool_info.initial_A_time = current_timestamp;
        pool_info.future_A_time = current_timestamp;
        // now (block.timestamp < t1) is always false, so we return saved A
    }
}