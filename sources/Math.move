module Owner::Math {
    public fun diff(a: u128, b: u128): u128 {
        if (a > b) {
            a - b
        } else {
            b - a
        }
    }
}
