pub fn init(state: (), website_key: SigningKey) -> UserState {
    let logged_interest_counter = 0u8;
    let interests = InterestBuffer {
        index: 0u8,
        buffer: [UserInterest::None; 16],
    };
    let signed = sign(interests, website_key);
    UserState {
        signature: signed,
        interests: interests,
    }
}

pub fn log_interest(state: UserState, website_visit: WebsiteVisit) -> LogResult {
    if is_signature_ok(state, website_visit.key) {
        let index = state.interests.index;
        let user_interest = website_visit.interest;
        let updated_interests = InterestBuffer {
            index: (index + 1) % 16,
            buffer: state.interests.buffer.update(index as usize, user_interest),
        };
        let updated_signature = sign(updated_interests, website_visit.key);
        let updated_state = UserState {
            signature: updated_signature,
            interests: updated_interests,
        };
        LogResult::Ok(updated_state)
    } else {
        LogResult::InvalidSignature
    }
}

pub fn decide_ad(state: UserState, website_key: SigningKey) -> AdDecisionResult {
    if is_signature_ok(state, website_key) {
        let sums = [0u8; 6]; // for the 6 user interests
        let interests = state.interests.buffer;
        let sums = interests.fold(sums, |sums: [u8; 6], interest: UserInterest| -> [u8; 6] {
            match interest {
                UserInterest::None => sums,
                UserInterest::Luxury => sums.update(1, sums[1] + 1),
                UserInterest::Cars => sums.update(2, sums[2] + 1),
                UserInterest::Politics => sums.update(3, sums[3] + 1),
                UserInterest::Sports => sums.update(4, sums[4] + 1),
                UserInterest::Arts => sums.update(5, sums[5] + 1),
            }
        });
        let max_interest = 0..6.fold(
            MaxInterest {
                visits: 0u8,
                index_of_variant: 0usize,
            },
            |max_interest: MaxInterest, i: usize| -> MaxInterest {
                if sums[i] > max_interest.visits {
                    MaxInterest {
                        index_of_variant: i,
                        visits: sums[i],
                    }
                } else {
                    max_interest
                }
            },
        );
        AdDecisionResult::Ok(match max_interest.index_of_variant {
            0 => UserInterest::None,
            1 => UserInterest::Luxury,
            2 => UserInterest::Cars,
            3 => UserInterest::Politics,
            4 => UserInterest::Sports,
            5 => UserInterest::Arts,
            _ => UserInterest::None,
        })
    } else {
        AdDecisionResult::InvalidSignature
    }
}

fn is_signature_ok(user_state: UserState, website_key: SigningKey) -> bool {
    // todo:
    true
}

fn sign(interests: InterestBuffer, website_key: SigningKey) -> u128 {
    // todo:
    0
}

struct UserState {
    signature: u128,
    interests: InterestBuffer,
}

struct InterestBuffer {
    index: u8,
    buffer: [UserInterest; 16],
}

struct WebsiteVisit {
    interest: UserInterest,
    key: SigningKey,
}

enum UserInterest {
    None,
    Luxury,
    Cars,
    Politics,
    Sports,
    Arts,
}

struct SigningKey {
    key: u128,
}

enum LogResult {
    InvalidSignature,
    Ok(UserState),
}

enum AdDecisionResult {
    InvalidSignature,
    Ok(UserInterest),
}

struct MaxInterest {
    index_of_variant: usize,
    visits: u8,
}
