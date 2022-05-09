pub fn init(website_key: SigningKey, state: ()) -> UserState {
    let logged_interest_counter = 0u8;
    let interests = [UserInterest::None; 16];
    let signed = sign(interests, website_key);
    UserState {
        signature: signed,
        interests: interests,
    }
}

pub fn log_interest(website_visit: WebsiteVisit, state: UserState) -> LogResult {
    if is_signature_ok(state, website_visit.key) {
        let interests = state.interests;
        let user_interest = website_visit.interest;
        let updated_interests = 0usize..16usize.map(|i: usize| -> UserInterest {
            if i == 0usize {
                user_interest
            } else {
                interests[i - 1usize]
            }
        });
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

pub fn decide_ad(website_key: SigningKey, state: UserState) -> AdDecisionResult {
    if is_signature_ok(state, website_key) {
        let sums = [0u8; 6]; // for the 6 user interests
        let interests = state.interests;
        let sums = interests.fold(sums, |sums: [u8; 6], interest: UserInterest| -> [u8; 6] {
            match interest {
                UserInterest::None => sums,
                UserInterest::Luxury => sums.update(1usize, sums[1] + 1u8),
                UserInterest::Cars => sums.update(2usize, sums[2] + 1u8),
                UserInterest::Politics => sums.update(3usize, sums[3] + 1u8),
                UserInterest::Sports => sums.update(4usize, sums[4] + 1u8),
                UserInterest::Arts => sums.update(5usize, sums[5] + 1u8),
            }
        });
        let max_interest = 0usize..6usize.fold(
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
            0u8 => UserInterest::None,
            1u8 => UserInterest::Luxury,
            2u8 => UserInterest::Cars,
            3u8 => UserInterest::Politics,
            4u8 => UserInterest::Sports,
            5u8 => UserInterest::Arts,
            _ => UserInterest::None,
        })
    } else {
        AdDecisionResult::InvalidSignature
    }
}

fn interest_as_u8(interest: UserInterest) -> u8 {
    match interest {
        UserInterest::None => 0u8,
        UserInterest::Luxury => 1u8,
        UserInterest::Cars => 2u8,
        UserInterest::Politics => 3u8,
        UserInterest::Sports => 4u8,
        UserInterest::Arts => 5u8,
        UserInterest::None => 6u8,
    }
}

fn is_signature_ok(state: UserState, website_key: SigningKey) -> bool {
    let bytes = state.interests.map(|interest: UserInterest| -> u8 {
        interest_as_u8(interest)
    });
    let st = absorb(bytes);
    let st = absorb_cont(st, website_key.key);
    let hash = squeeze(st);
    hash == state.signature
}

fn sign(interests: [UserInterest; 16], website_key: SigningKey) -> [u8; 16] {
    let bytes = interests.map(|interest: UserInterest| -> u8 {
        interest_as_u8(interest)
    });
    let st = absorb(bytes);
    let st = absorb_cont(st, website_key.key);
    let hash = squeeze(st);
    hash
}

fn absorb(bin: [u8; 16]) -> [u8; 48] {
    let st = [0u8; 48];
    down(st, bin, 1u8)
}

fn absorb_cont(st: [u8; 48], bin: [u8; 16]) -> [u8; 48] {
    let st1 = u8_to_u32_arr(st);
    let st2 = permute(st1);
    let st3 = u32_to_u8_arr(st2);
    down(st3, bin, 0u8)
}

fn swap(st: [u32; 12], a: usize, b: usize) -> [u32; 12] {
    let st1 = st.update(a, st[b]);
    let st2 = st1.update(b, st[a]);
    st2
}

fn round(st: [u32; 12], round_key: u32) -> [u32; 12] {
    // for i in 0..4 {
    //    e[i] = rotate_right(st[i] ^ st[i + 4] ^ st[i + 8], 18);
    //    e[i] ^= rotate_right(e[i], 9);
    // }
    let e = 0usize..4usize.map(|i: usize| -> u32 {
        let e = rotate_right(st[i] ^ st[i + 4usize] ^ st[i + 8usize], 18u8);
        let e = e ^ rotate_right(e, 9u8);
        e
    });

    // for i in 0..12 {
    //     st[i] ^= e[(i.wrapping_sub(1)) & 3];
    // }
    let st = [
        st[0] ^ e[3],
        st[1] ^ e[0],
        st[2] ^ e[1],
        st[3] ^ e[2],
        st[4] ^ e[3],
        st[5] ^ e[0],
        st[6] ^ e[1],
        st[7] ^ e[2],
        st[8] ^ e[3],
        st[9] ^ e[0],
        st[10] ^ e[1],
        st[11] ^ e[2],
    ];

    let st = swap(st, 7usize, 4usize);
    let st = swap(st, 7usize, 5usize);
    let st = swap(st, 7usize, 6usize);
    let st = st.update(0usize, st[0] ^ round_key);

    // for i in 0..4 {
    //     let a = st[i];
    //     let b = st[i + 4];
    //     let c = st[i + 8].rotate_right(21);
    //     st[i + 8] = ((b & !a) ^ c).rotate_right(24);
    //     st[i + 4] = ((a & !c) ^ b).rotate_right(31);
    //     st[i] ^= c & !b;
    // }
    let st = 0usize..4usize.fold(st, |st: [u32; 12], i: usize| -> [u32; 12] {
        let a = st[i];
        let b = st[i + 4usize];
        let c = rotate_right(st[i + 8usize], 21u8);
        let st = st.update(i + 8usize, rotate_right((b & !a) ^ c, 24u8));
        let st = st.update(i + 4usize, rotate_right((a & !c) ^ b, 31u8));
        let st = st.update(i, st[i] ^ (c & !b));
        st
    });

    let st = swap(st, 8usize, 10usize);
    let st = swap(st, 9usize, 11usize);

    st
}

fn permute(st: [u32; 12]) -> [u32; 12] {
    let ROUND_KEYS = [
        88u32, 56u32, 960u32, 208u32, 288u32, 20u32, 96u32, 44u32, 896u32, 240u32, 416u32, 18u32,
    ];

    0usize..12usize.fold(st, |st: [u32; 12], i: usize| -> [u32; 12] {
        round(st, ROUND_KEYS[i])
    })
}

fn squeeze(st: [u8; 48]) -> [u8; 16] {
    let st = u8_to_u32_arr(st);
    let st = permute(st);
    [
        st[0] as u8,
        (st[0] >> 8u8) as u8,
        (st[0] >> 16u8) as u8,
        (st[0] >> 24u8) as u8,
        st[1] as u8,
        (st[1] >> 8u8) as u8,
        (st[1] >> 16u8) as u8,
        (st[1] >> 24u8) as u8,
        st[2] as u8,
        (st[2] >> 8u8) as u8,
        (st[2] >> 16u8) as u8,
        (st[2] >> 24u8) as u8,
        st[3] as u8,
        (st[3] >> 8u8) as u8,
        (st[3] >> 16u8) as u8,
        (st[3] >> 24u8) as u8,
    ]
}

fn down(st: [u8; 48], bin: [u8; 16], cd: u8) -> [u8; 48] {
    let st = add_bytes(st, bin);
    let st = add_byte(st, 1u8, 16usize);
    add_byte(st, cd, 47usize)
}

fn rotate_right(val: u32, rotation: u8) -> u32 {
    (val >> rotation) ^ (val << (32u8 - rotation))
}

fn u8_to_u32_arr(st: [u8; 48]) -> [u32; 12] {
    0usize..12usize.map(|i: usize| -> u32 { u8_to_u32(st, i * 4usize) })
}

fn u32_to_u8_arr(st: [u32; 12]) -> [u8; 48] {
    [
        st[0] as u8,
        (st[0] >> 8u8) as u8,
        (st[0] >> 16u8) as u8,
        (st[0] >> 24u8) as u8,
        st[1] as u8,
        (st[1] >> 8u8) as u8,
        (st[1] >> 16u8) as u8,
        (st[1] >> 24u8) as u8,
        st[2] as u8,
        (st[2] >> 8u8) as u8,
        (st[2] >> 16u8) as u8,
        (st[2] >> 24u8) as u8,
        st[3] as u8,
        (st[3] >> 8u8) as u8,
        (st[3] >> 16u8) as u8,
        (st[3] >> 24u8) as u8,
        st[4] as u8,
        (st[4] >> 8u8) as u8,
        (st[4] >> 16u8) as u8,
        (st[4] >> 24u8) as u8,
        st[5] as u8,
        (st[5] >> 8u8) as u8,
        (st[5] >> 16u8) as u8,
        (st[5] >> 24u8) as u8,
        st[6] as u8,
        (st[6] >> 8u8) as u8,
        (st[6] >> 16u8) as u8,
        (st[6] >> 24u8) as u8,
        st[7] as u8,
        (st[7] >> 8u8) as u8,
        (st[7] >> 16u8) as u8,
        (st[7] >> 24u8) as u8,
        st[8] as u8,
        (st[8] >> 8u8) as u8,
        (st[8] >> 16u8) as u8,
        (st[8] >> 24u8) as u8,
        st[9] as u8,
        (st[9] >> 8u8) as u8,
        (st[9] >> 16u8) as u8,
        (st[9] >> 24u8) as u8,
        st[10] as u8,
        (st[10] >> 8u8) as u8,
        (st[10] >> 16u8) as u8,
        (st[10] >> 24u8) as u8,
        st[11] as u8,
        (st[11] >> 8u8) as u8,
        (st[11] >> 16u8) as u8,
        (st[11] >> 24u8) as u8,
    ]
}

fn u8_to_u32(st: [u8; 48], base_idx: usize) -> u32 {
    st[base_idx] as u32
        ^ ((st[base_idx + 1usize] as u32) << 8u8)
        ^ ((st[base_idx + 2usize] as u32) << 16u8)
        ^ ((st[base_idx + 3usize] as u32) << 24u8)
}

fn add_byte(st: [u8; 48], byte: u8, offset: usize) -> [u8; 48] {
    st.update(offset, st[offset] ^ byte)
}

fn add_bytes(st: [u8; 48], chunk: [u8; 16]) -> [u8; 48] {
    0usize..16usize.fold(st, |st: [u8; 48], i: usize| -> [u8; 48] {
        add_byte(st, chunk[i], i)
    })
}

struct UserState {
    signature: [u8; 16],
    interests: [UserInterest; 16],
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
    key: [u8; 16],
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
