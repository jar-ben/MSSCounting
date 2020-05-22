import glob

def maxVar(C):
    m = 0
    for cl in C:
        for l in cl:
            m = max(m,abs(l))
    return m

def randomBool():
    return bool(random.getrandbits(1))

def exportCNF(clauses, filename, ind = []):
    with open(filename, "w") as f:
        if len(ind) > 0:
            f.write("c ind " + " ".join([str(i) for i in ind]) + " 0\n")
        maxVar = max([max(abs(l) for l in cl) for cl in clauses])
        f.write("p cnf {} {}\n".format(maxVar, len(clauses)))
        for cl in clauses:
            f.write(" ".join([str(l) for l in cl]) + " 0\n")

def sign(l):
    if l > 0: return 1
    return -1

def renumber(cls):
    vars = []
    for cl in cls:
        for l in cl:
            if abs(l) not in vars:
                vars.append(abs(l))
    vars = sorted(vars)
    mapa = {}
    for i in range(len(vars)):
        mapa[vars[i]] = i + 1
    renamed = []
    for cl in cls:
        renamed.append([sign(l) * mapa[abs(l)] for l in cl])
    return renamed

def refine(filename, target):
    with open(filename, "r") as f:
        lines = [l.strip() for l in f.readlines()]
        cls = []
        for line in lines:
            if line[0] in ["p", "c"]: continue
            cls.append(sorted([int(l) for l in line.split()[:-1]]))
    uniques = set([tuple(cl) for cl in cls])
    ucls = []
    for cl in uniques:
        ucls.append([l for l in cl])
    renumbered = renumber(ucls)
    exportCNF(renumbered, target)

for file in glob.glob("./randBenchs/*.cnf"):
    print(file)
    target = file[:-4] + "_refined.cnf"
    print(file, target)
    refine(file, target)
