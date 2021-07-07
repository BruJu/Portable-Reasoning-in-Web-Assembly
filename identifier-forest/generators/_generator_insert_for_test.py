import random

# TODO : complete this file to generate units tests

SIZE = 20
Q = 4



def make_quad():
    return ", ".join([str(random.randrange(0, 200)) for _ in range(Q)])



for _ in range(SIZE):
    print("tree.insert([{}]);".format(make_quad()))



for i in range(16):
    s = random.randrange(0, 1000)
    p = random.randrange(0, 1000)
    o = random.randrange(0, 1000)
    g = random.randrange(0, 1000)

    print("    assert!(pattern_match(&[{}, {}, {}, {}], &[{}, {}, {}, {}]));"
        .format(s, p, o, g,
            "Some("  + str(s) + ")" if (i % 8) == 0 else "None",
            "Some("  + str(p) + ")" if (i % 4) == 0 else "None",
            "Some("  + str(o) + ")" if (i % 2) == 0 else "None",
            "Some("  + str(g) + ")" if (i % 1) == 0 else "None",
        )
    )

for i in range(32):
    s = random.randrange(0, 1000)
    p = random.randrange(0, 1000)
    o = random.randrange(0, 1000)
    g = random.randrange(0, 1000)

    ss = random.randrange(0, 1000) if random.randrange(0, 2) == 1 else s
    sp = random.randrange(0, 1000) if random.randrange(0, 2) == 1 else p
    so = random.randrange(0, 1000) if random.randrange(0, 2) == 1 else o
    sg = random.randrange(0, 1000) if random.randrange(0, 2) == 1 else g

    if s == ss and p == sp and s == so and g == sg:
        continue

    print("    assert!(!pattern_match(&[{}, {}, {}, {}], &[{}, {}, {}, {}]));"
        .format(s, p, o, g,
            "Some("  + str(ss) + ")" if (i % 8) == 0 else "None",
            "Some("  + str(sp) + ")" if (i % 4) == 0 else "None",
            "Some("  + str(so) + ")" if (i % 2) == 0 else "None",
            "Some("  + str(sg) + ")" if (i % 1) == 0 else "None",
        )
    )


