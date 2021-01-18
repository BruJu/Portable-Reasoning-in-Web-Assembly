positions = [
    ("Subject", "S", 0),
    ("Predicate", "P", 1),
    ("Object", "O", 2),
    ("Graph", "G", 3)
]

print("//! This module lists every possible permutation of")
print("//! [`Tree4Profile`](crate::compile_time_forest::Tree4Profile)")
print("//! order for a tree of quads.")
print("//! ")
print("//! These permutation are intended to be used")
print("//! as parameters for the [`CTForest`](crate::compile_time_forest::CTForest)")
print("//! class")

def every_order():
    retval = []
    for a in positions:
        for b in positions:
            for c in positions:
                for d in positions:
                    if a != b and a != c and a != d and b != c and b != d and c != d:
                        retval.append([a, b, c, d])

    return retval

all = every_order()

print("use super::*;")
print("")

for a in all:
    spog = "".join([x[1] for x in a])

    print()
    print("/// Profile for a lazy tree whose order")
    print("/// will be {}".format(" > ".join(x[0] for x in a)))
    print("pub struct {} {}".format(spog, "{}"))
    print("impl Tree4Profile for {} {}".format(spog, "{"))
    print("    type First = {};".format(a[0][0]))
    print("    type Second = {};".format(a[1][0]))
    print("    type Third = {};".format(a[2][0]))
    print("    type Fourth = {};".format(a[3][0]))
    print("    const ALWAYS_INSTANCIATED: bool = false;")
    print("}")

    spog = "".join([x[1] for x in a]) + "Always"
    print()
    print("/// Profile for a tree that is always instanciated and whose order")
    print("/// is {}".format(" > ".join(x[0] for x in a)))
    print("pub struct {} {}".format(spog, "{}"))
    print("impl Tree4Profile for {} {}".format(spog, "{"))
    print("    type First = {};".format(a[0][0]))
    print("    type Second = {};".format(a[1][0]))
    print("    type Third = {};".format(a[2][0]))
    print("    type Fourth = {};".format(a[3][0]))
    print("    const ALWAYS_INSTANCIATED: bool = true;")
    print("}")

