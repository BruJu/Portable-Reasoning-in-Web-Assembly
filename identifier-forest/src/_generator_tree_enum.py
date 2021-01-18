import re

# python src/_generator_tree_enum.py > src/run_time_forest/_dynamic.rs

def extract_parameters(l):
    r = ", ([a-zA-Z_0-9]*)\: (&?)"

    m = re.findall(r, l)
    return ", ".join([x[1] + x[0] for x in m])

def read_trait_description(filename, trait_name):
    r = "^fn ([a-z_]*)(\<[a-z'A-Z, ]*\>)?\(((.*)self)?([^)]*)\)( -> ([a-zA-Z0-9<>', ]*))?( where (.*))?;$"

    with open(filename) as f:
        lines = f.readlines()
    
    result = { "where_clause" : "", "methods": [] }
    level = 0
    is_this_trait = False

    for l in lines:
        l = l.strip()

        if l == "":
            continue
        elif l[0:2] == "//":
            continue
        elif l == "{":
            level += 1
        elif l == "}":
            level -= 1
            if level == 0:
                is_this_trait = False
        elif l == "pub trait " + trait_name:
            is_this_trait = True
        else:
            if level > 1:
                print("More than one level")
                exit()
            
            if level == 1 and is_this_trait:
                m = re.search(r, l)
                if m is None:
                    print("Function not recognized")
                    print(l)
                    exit()

                def unnone(x):
                    return "" if x is None else x

                this_method = {}
                this_method["name"] = m.group(1)
                this_method["generic"] = unnone(m.group(2))
                this_method["self_parameter"] = unnone(m.group(3))
                this_method["self_args"] = unnone(m.group(4))
                this_method["other_parameters"] = unnone(m.group(5))
                this_method["return_type_"] = unnone(m.group(6))
                this_method["return_type"] = unnone(m.group(7))
                this_method["where_clause"] = unnone(m.group(8))
                this_method["forward"] = extract_parameters(unnone(m.group(5)))
                
                result["methods"].append(this_method)
            
            if level == 0 and is_this_trait:
                if result["where_clause"] != "":
                    print("More than one where clause")
                    print(result["where_clause"])
                    print(l)
                    exit()
                
                result["where_clause"] = l

    return result

import pprint as pp


positions = [
    ("Subject", "S", 0),
    ("Predicate", "P", 1),
    ("Object", "O", 2),
    ("Graph", "G", 3)
]

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

output = []
n = "DynamicOnceTreeSet<I>"

def add(s = ""):
    #print(s)
    output.append(s)

# ===============
# ENUM DEFINITION

add("use crate::tree::OnceTreeSet;")
add("use crate::order::{ Subject, Predicate, Object, Graph };")
add("use crate::tree::{ Tree4Iterator, LazyStructure, MaybeTree4 };")
add("use crate::Identifier;")

add("")



add("/// A MaybeTree4 implementation whose order is decided at execution time.")
add("///")
add("/// The choice is made by using the appropriate constructor with the position order")
add("/// in the constructor instead of generic parameters. The appropriate OnceTreeSet")
add("/// will be created depending on the given order, and then this structure will act")
add("/// as the desired OnceTreeSet by forwarding the calls to the different methods.")
add("pub enum " + n)
add("where I: Identifier")
add("{")

for permutation in all:
    add("    {}(OnceTreeSet<I{}>),".format(
        "".join([x[1] for x in permutation]),
        "".join([", " + x[0] for x in permutation])
    ))

add("}")

add()
add()

# ===============
# LazyStructure usage

lazy_structure = read_trait_description("src/tree/_tree_trait.rs", "LazyStructure")

add("impl<I> " + n)
add("where I: Identifier")
add("{")


documentation = {}

documentation["new"] = [
    "Builds a new TreeSet whose order is defined at execution time. The tree",
    "is not directly built (the underlying used constructor is the new function",
    "from the OnceTreeSet class)",
    "",
    "See OnceTreeSet for more details"
]

documentation["new_instanciated"] = [
    "Builds a new TreeSet whose order is defined at execution time. The tree",
    "is directly built and ready for usage (according to new_instanciated",
    "specificaiton)",
    "",
    "See OnceTreeSet for more details"
]


for method in lazy_structure["methods"]:
    for l in documentation[method["name"]]:
        add("    /// " + l)
    add("    pub fn "+ method["name"] + "(order: &[usize; 4]) -> Option<"+n+"> {")
    add("        match order {")

    for permutation in all:
        
        add("            [{}] => Some(Self::{}( OnceTreeSet::{}() )),".format(
            ", ".join([str(x[2]) for x in permutation]),
            "".join([x[1] for x in permutation]),
            method["name"]
        ))

    add("            [_, _, _, _] => None,")
    add("        }")
    add("    }")
    add("")

add("}")

add("")

# ===============
# MaybeTree4 implementation


# print("\n".join(output))

maybe_tree = read_trait_description("src/tree/_tree_trait.rs", "MaybeTree4<I>")

#pp.pprint(maybe_tree)

add("impl<I> MaybeTree4<I> for " + n)
add("where I: Identifier")
add("{")

for method in maybe_tree["methods"]:
    add("    fn "+ method["name"] + method["generic"] + "("+ method["self_parameter"] + method["other_parameters"] +")" + method["return_type_"] + method["where_clause"] + " {")

    #print(method)

    if method["self_parameter"].find("mut") == -1:
        self_ = "&self"
    else:
        self_ = "self"

    add("        match " + self_ + " {")

    for permutation in all:

        add("            Self::{}(tree) => tree.{}({}),".format(
            "".join([x[1] for x in permutation]),
            method["name"],
            method["forward"]
        ))


    add("        }")
    add("    }")
    add("")

add("}")

add("")

print("\n".join(output))
