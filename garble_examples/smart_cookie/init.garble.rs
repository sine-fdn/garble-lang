fn main(user_state: (), website_key: u128) -> (u128, (u8, [UserInterest; 16])) {
    let logged_interest_counter = 0u8;
    let user_state = (logged_interest_counter, [UserInterest::None; 16]);
    let signed = sign(user_state, website_key);
    (signed, user_state)
}

fn sign(user_state: (u8, [UserInterest; 16]), website_signing_key: u128) -> u128 {
    // todo:
    0
}

enum UserInterest {
    None,
    Luxury,
    Cars,
    Politics,
    Sports,
    Arts,
}
