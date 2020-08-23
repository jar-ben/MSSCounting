import sys
from math import log
import subprocess as sp
import random
import time
from statistics import median
from random import randint
import argparse

def run(cmd, timeout, ttl = 3):
    proc = sp.Popen([cmd], stdout=sp.PIPE, stderr=sp.PIPE, shell=True)
    try:
        (out, err) = proc.communicate(timeout = int(timeout * 1.1) + 1)
        out = out.decode("utf-8")
    except sp.TimeoutExpired:
        proc.kill()
        try:
            (out, err) = proc.communicate()
            out = out.decode("utf-8")
        except ValueError:
            if ttl > 0:
                return run(cmd, timeout, ttl - 1)
            out = ""
    return out

def maxVar(C):
    m = 0
    for cl in C:
        for l in cl:
            m = max(m,abs(l))
    return m

def randomBool():
    return bool(random.getrandbits(1))

def exportCNF(clauses, filename, ind, varFile):
    print("running export for ", filename)
    with open(filename, "w") as f:
        if len(ind) > 0:
            f.write("c ind " + " ".join([str(i) for i in ind]) + " 0\n")
        maxVar = max([max(abs(l) for l in cl) for cl in clauses])
        f.write("p cnf {} {}\n".format(maxVar, len(clauses)))
        for cl in clauses:
            f.write(" ".join([str(l) for l in cl]) + " 0\n")

    print(varFile)
    with open(varFile, "w") as f:
        f.write(",".join ([str(v) for v in ind]))

#parse .gcnf instance,
#returns a pair C,B where B contains the base (hard) clauses and C the other clauses
def parse(filename):
    C = []
    B = []
    with open(filename, "r") as f:
        lines = f.readlines()
        if filename[-5:] == ".gcnf":
            for line in lines[1:]:
                if line[0] in ["p","c"]: continue
                line = line.split(" ")
                cl = [int(i) for i in line[1:-1]]
                if len(cl) > 0:
                    if line[0] == "{0}":
                        B.append(cl)
                    else:
                        C.append(cl)
        else:
            for line in lines[1:]:
                if line[0] in ["p","c"]: continue
                line = line.split(" ")
                cl = [int(i) for i in line[:-1]]
                if len(cl) > 0:
                    C.append(cl)
    return C,B

def offset(a, off):
    if a > 0:
        return a + off
    return a - off

class Counter:
    def __init__(self, filename):
        self.variant = "base"
        self.filename = filename
        self.C, self.B = parse(filename)
        self.autarky = True
        if self.autarky and filename[-4:] == ".cnf":
            self.autarkyTrim()

        self.dimension = len(self.C)
        self.XOR = None
        self.checks = 0
        self.rid = randint(1,10000000)
        flatten = []
        for cl in (self.B + self.C):
            flatten += cl
        self.lits = set([l for l in flatten])
        self.hitmapC = {l:[] for l in self.lits}
        for i in range(len(self.C)):
            for l in self.C[i]:
                assert l in self.lits
                self.hitmapC[l].append(i + 1) #+1 offset
        self.hitmapB = {l:[] for l in self.lits}
        for i in range(len(self.B)):
            for l in self.B[i]:
                assert l in self.lits
                self.hitmapB[l].append(i) #note that here we store 0-based index as opposed to hitmapC

    def autarkyTrim(self):
        assert self.B == []
        out = run("timeout 3600 python3 autarky.py {}".format(self.filename), 3600)
        if "autarky vars" in out:
            for line in out.splitlines():
                line = line.rstrip()
                if line[:2] == "v ":
                    autarky = [int(c) - 1 for c in line.split()[1:]]
        coAutarky = [i for i in range(len(self.C)) if i not in autarky]
        C = [self.C[c] for c in autarky]
        B = [self.C[c] for c in coAutarky]
        print("autarky size: {} of {} clauses".format(len(autarky), len(self.C)))
        self.C, self.B = C, B

    def SS(self):
        return self.W4()

    def LSS(self):
        return self.R4()


    #VARIABLES INFO
    #Activation literals A: 1 -- dimension
    #Activation literals B: dimension + 1 -- 2*dimension
    #F's variables: 2*dimension + 1 -- 2*dimension + Vars(F)
    def W1(self):
        clauses = []

        i = 1
        for cl in self.C:
            renumCl = []
            for l in cl:
                if l > 0: renumCl.append(l + 2*self.dimension)
                else: renumCl.append(l - 2*self.dimension)
            renumCl.append(i)
            clauses.append(renumCl)
            i += 1
        for cl in self.B:
            renumCl = []
            for l in cl:
                if l > 0: renumCl.append(l + 2*self.dimension)
                else: renumCl.append(l - 2*self.dimension)
            clauses.append(renumCl)
        return clauses, [i for i in range(1, self.dimension + 1)]
        
    def nonMSSBase(self):
        clauses = []
        #E is sat
        i = 1
        for cl in self.C:
            renumCl = []
            for l in cl:
                if l > 0: renumCl.append(l + 2*self.dimension)
                else: renumCl.append(l - 2*self.dimension)
            renumCl.append(i + self.dimension)
            clauses.append(renumCl)
            i += 1

        #E supseteq S
        for i in range(1, self.dimension + 1):
            clauses.append([i, - (i + self.dimension)])

        proper = []
        mv = maxVar(clauses)
        act = mv
        for i in range(1, self.dimension + 1):
            act += 1
            proper += [[act, i], [act, -(i + self.dimension)]] 
        proper.append([-a for a in range(mv + 1, act + 1)])

        clauses += proper
        return clauses
 
    def R1(self):
        clauses, inds = self.W1()
        return clauses + self.nonMSSBase(), inds

    def W4(self):
        clauses, inds = self.W1()

        #max model
        i = 1
        for cl in self.C:
            renumCl = []
            for l in cl:
                if l > 0:
                    clauses.append([-i, -(l + 2*self.dimension)])
                else:
                    clauses.append([-i, -(l - 2*self.dimension)])
            i += 1

        return clauses, inds

    def R4(self):
        clauses, inds = self.W4()
        return clauses + self.nonMSSBase(), inds

    def parseGanak(self, out):
        if "# END" not in out: return -1
        reading = False
        for line in out.splitlines():
            if reading:
                return int(line.rstrip().split()[-1])
            if "# solutions" in line: reading = True

    def parseProjMC(self, out):
        for line in out.splitlines():
            if line[:2] == "s ":
                return int(line.rstrip().split()[1])

    def runExact(self):
        self.ganak = True
        SSClauses, SSInd = self.SS()
        SSFile = "/var/tmp/SS_{}.cnf".format(self.rid)
        SSIndFile = SSFile[:-4] + "_{}.cnf".format(len(SSInd))
        exportCNF(SSClauses, SSFile, SSInd, SSIndFile)
        print(SSFile)
        
        LSSClauses, LSSInd = self.LSS()
        LSSFile = "/var/tmp/LSS_{}.cnf".format(self.rid)
        LSSIndFile = LSSFile[:-4] + "_{}.cnf".format(len(LSSInd))
        exportCNF(LSSClauses, LSSFile, LSSInd, LSSIndFile)
        print(LSSFile)

        timeout = 3600
        if self.ganak:
            cmd = "timeout {} /home/xbendik/bin/ganak/build/ganak {}".format(timeout, SSFile)
            print(cmd)
            SScount = self.parseGanak(run(cmd, timeout))
            print("SS count:", SScount)

            cmd = "timeout {} /home/xbendik/bin/ganak/build/ganak {}".format(timeout, LSSFile)
            print(cmd)
            LSScount = self.parseGanak(run(cmd, timeout))
            print("LSS count:", LSScount)
        else:
            cmd = "timeout {} ./projMC_linux {} -fpv=\"{}\"".format(timeout, SSFile, SSIndFile)
            print(cmd)
            SScount = self.parseProjMC(run(cmd, timeout))
            print("SS count:", SScount)

            cmd = "timeout {} ./projMC_linux {} -fpv=\"{}\"".format(timeout, LSSFile, LSSIndFile)
            print(cmd)
            LSScount = self.parseProjMC(run(cmd, timeout))
            print("LSS count:", LSScount)
            
        print("MSS count:", SScount - LSScount)

import sys
if __name__ == "__main__":
    parser = argparse.ArgumentParser("MSS counter")
    parser.add_argument("--verbose", "-v", action="count", help = "Use the flag to increase the verbosity of the outputs. The flag can be used repeatedly.")
    parser.add_argument("--variant", help = "Type of endocing (allowed values = {base,B,FEB}", default = "base")
    parser.add_argument("input_file", help = "A path to the input file. Either a .cnf or a .gcnf instance. See ./examples/")
    args = parser.parse_args()

    counter = Counter(args.input_file)
    counter.variant = args.variant

    counter.runExact()
