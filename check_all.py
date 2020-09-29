#!/usr/bin/env python3

import glob
import os
import re
import subprocess
import time

def generate(logic):
    ia = any([l in logic for l in ['IDL', 'LIA', 'LIRA', 'NIA', 'NIRA']])
    ra = any([l in logic for l in ['LIRA', 'LRA', 'NIRA', 'NRA', 'RDL']])
    lname = ''.join(logic)
    if lname == 'QF_A':
        lname = 'QF_AX'

    filename = 'tcbench/{}.generated.smt2'.format(lname)
    benchlogics[filename] = logic

    if 'T' in logic:
        if not 'NRA' in logic:
            return
    decls = []
    asserts = []
    decls.append('(set-logic {})'.format(lname))
    decls.append('(declare-fun b () Bool)')
    if 'A' in logic:
        if lname == 'QF_AX':
            decls.append('(declare-fun a () (Array Bool Bool))')
            asserts.append('(= (select a b) (not (select a (not b))))')
            decls.append('(declare-sort Index 0)')
            decls.append('(declare-sort Element 0)')
            decls.append('(declare-fun ax1 () (Array Index Element))')
            decls.append('(declare-fun ax2 () (Array Index Element))')
            decls.append('(declare-fun aid () Index)')
            decls.append('(declare-fun ael () Element)')
            asserts.append('(= ax1 (store ax2 aid (select ax1 aid)))')
    if 'UF' in logic:
        decls.append('(declare-sort S1 0)')
        decls.append('(declare-sort S2 0)')
        decls.append('(declare-fun uf1 () S1)')
        decls.append('(declare-fun uf2 () S2)')
        decls.append('(declare-fun uf3 (S1) S2)')
        decls.append('(declare-fun uf4 (S1 S2) Bool)')
        asserts.append('(not (uf4 uf1 (uf3 uf1)))')
        asserts.append('(uf4 uf1 uf2)')
    if 'BV' in logic:
        decls.append('(declare-fun bv () (_ BitVec 8))')
        asserts.append('(= b (bvuge bv (bvneg bv)))')
    if 'FP' in logic:
        decls.append('(declare-fun fprm () RoundingMode)')
        decls.append('(declare-fun fpv () (_ FloatingPoint 8 24))')
        asserts.append('(= b (fp.lt fpv (fp.mul fprm fpv fpv)))')
    if 'DT' in logic:
        decls.append('(declare-datatypes ((DT 0)) (((None) (Some (i Bool)))))')
        # Todo: add some assertion here
    if ia:
        decls.append('(declare-fun i1 () Int)')
        decls.append('(declare-fun i2 () Int)')
        asserts.append('(and (> i1 5) (>= i2 3))')
    if ra:
        decls.append('(declare-fun r1 () Real)')
        decls.append('(declare-fun r2 () Real)')
        asserts.append('(and (> r1 5) (> 6 r2) (> r2 0))')
    if 'S' in logic:
        decls.append('(declare-fun s () String)')
        asserts.append('(str.in_re s (str.to_re "ab+c"))')
    if 'T' in logic:
        asserts.append('(> r1 (tan r2))')
    
    if 'A' in logic and 'UF' in logic:
        decls.append('(declare-fun auf () (Array S1 S2))')
        decls.append('(declare-fun ufa ((Array S1 S2)) S2)')
        asserts.append('(= (select auf uf1) (ufa auf))')
    if 'A' in logic and 'BV' in logic:
        decls.append('(declare-fun abv () (Array (_ BitVec 8) (_ BitVec 8)))')
        asserts.append('(= (select abv bv) (bvnot (select abv (bvneg bv))))')
    if 'A' in logic and 'FP' in logic:
        decls.append('(declare-fun afp () (Array (_ FloatingPoint 8 24) (_ FloatingPoint 8 24)))')
        asserts.append('(= (select afp fpv) (fp.neg (select afp (fp.neg fpv))))')
    if 'A' in logic and 'DT' in logic:
        pass
    if 'A' in logic and ia:
        decls.append('(declare-fun ai () (Array Int Int))')
        asserts.append('(> (select ai i1) (select (store ai i1 (+ i1 i2)) i2))')
    if 'A' in logic and ra:
        decls.append('(declare-fun ar () (Array Real Real))')
        asserts.append('(> (select ar r1) (select (store ar r1 (- r1 r2)) r2))')
    if 'A' in logic and 'S' in logic:
        pass

    if 'UF' in logic and 'BV' in logic:
        decls.append('(declare-fun bvuf ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))')
        asserts.append('(bvsge (bvneg bv) (bvnot (bvuf bv (bvneg bv))))')
    if 'UF' in logic and 'FP' in logic:
        pass
    if 'UF' in logic and 'DT' in logic:
        pass
    if 'UF' in logic and ia:
        pass
    if 'UF' in logic and ra:
        pass
    if 'UF' in logic and 'S' in logic:
        pass

    if 'BV' in logic and 'FP' in logic:
        asserts.append('(= ((_ fp.to_ubv 8) fprm fpv) bv)')
    if 'BV' in logic and 'DT' in logic:
        pass
    if 'BV' in logic and ia:
        pass
    if 'BV' in logic and ra:
        pass
    if 'BV' in logic and 'S' in logic:
        pass

    if 'FP' in logic and 'DT' in logic:
        pass
    if 'FP' in logic and ia:
        pass
    if 'FP' in logic and ra:
        pass
    if 'FP' in logic and 'S' in logic:
        pass
    
    if 'DT' in logic and ia:
        pass
    if 'DT' in logic and ra:
        pass
    if 'DT' in logic and 'S' in logic:
        pass

    if ia and ra:
        asserts.append('(and (> i1 r1) (= r2 (+ i1 i2)))')
    if 'NIA' in logic or 'NIRA' in logic:
        asserts.append('(and (> i1 7) (= (* i1 i2) (* i1 i1 i1)))')
    if 'NIRA' in logic or 'NRA' in logic:
        asserts.append('(and (> r1 7) (= (* r1 r2) (* r1 r1 r1)))')
    if ia and 'S' in logic:
        asserts.append('(and (> (* (str.len s) (str.len s)) i1) (= (str.indexof s "a" i2) i1))')
    if ra and 'S' in logic:
        pass

    f = open(filename, 'w')
    for d in decls:
        f.write('{}\n'.format(d))
    for a in asserts:
        f.write('(assert {})\n'.format(a))
    f.write('(check-sat)\n')
    f.close()

import itertools
theories = [
    # Todo: add quantifiers
    ['QF_'],
    ['', 'A'],
    ['', 'UF'],
    ['', 'BV'],
    ['', 'FP'],
    ['', 'DT'],
    ['', 'S'],
    ['', 'IDL', 'LIA', 'LIRA', 'LRA', 'NIA', 'NIRA', 'NRA', 'RDL'],
    ['', 'T'],
]

benchlogics = {}

for comb in itertools.product(*theories):
    generate(comb)

inputs = sorted(glob.glob('tcbench/*.smt2'))
for i in inputs:
    if not i in benchlogics:
        benchlogics[i] = []

solvers = {
    'cvc4-1.8': ['bin/cvc4-1.8', '--strings-exp', '--nl-ext', '--nl-ext-tplanes'],
    'cvc4-0f77646': ['bin/cvc4-0f77646', '--strings-exp', '--theoryof-mode=type', '--nl-ext', '--nl-cad'],
    'mathsat-5.6': ['bin/mathsat-5.6.3'],
    'mathsat-5.5': ['bin/mathsat-5.5.4'],
    'smtinterpol-2.5': ['java', '-jar', 'bin/smtinterpol-2.5.jar'],
    'yices-2.6.2': ['bin/yices-smt2-2.6.2'],
    'z3-4.8.9': ['bin/z3-4.8.9'],
}

def run(cmd):
    proc = subprocess.Popen(cmd, stdout = subprocess.PIPE, stderr = subprocess.PIPE)
    try:
        out, err = proc.communicate(timeout = 5)
    except subprocess.TimeoutExpired:
        proc.kill()
        out, err = proc.communicate()
    return (out.decode('utf8').strip(), err.decode('utf8').strip())

def status(solver, out, err):

    if re.match('smtinterpol-.*', solver):
        if re.match('unsupported.*', out):
            return (['unsupported logic'], None, '', '')

    errors = []

    purger = [
        '; ignoring unsupported logic [A-Z_]+ line: [0-9]+ position: [0-9]+',
    ]

    for p in purger:
        err = re.sub(p, '', err, re.M)
        out = re.sub(p, '', out, re.M)

    res = {
        'ignoring unsupported logic ([A-Z_]+) line': 'unsupported logic {}',
        'logic ([A-Z_]+) is not supported': 'unsupported logic {}',
        'unknown command: ([a-zA-Z-]+)"': 'unsupported command {}',
        'unknown function/constant ([a-zA-Z_.]+)': 'unsupported {}',
        'unknown logic: ([A-Z_]+)': 'unknown logic {}',
        'unknown symbol: ([a-zA-Z-]+)"': 'unsupported symbol {}',
    }

    for r in res:
        m = re.search(r, err)
        if m != None:
            errors.append(res[r].format(*m.groups()))
        m = re.search(r, out)
        if m != None:
            errors.append(res[r].format(*m.groups()))

    if err != '' and errors == '':
        print("No errors detected within:\n{}".format(err))

    result = None
    if re.search('^sat$', out, flags = re.M) != None:
        result = 'sat'
    if re.search('^unsat$', out, flags = re.M) != None:
        result = 'unsat'
    if re.match('(un)?sat', out) != None:
        out = ''
    
    purger = [
        '; ignoring unsupported logic [A-Z_]+ line: [0-9]+ position: [0-9]+',
        '\(error "unknown logic: [A-Z_]+"\).*',
        '\(error "logic [A-Z_]+ is not supported"\).*',
    ]

    for p in purger:
        err = re.sub(p, '', err, flags = re.M | re.DOTALL)
        out = re.sub(p, '', out, flags = re.M | re.DOTALL)
    
    return (errors, result, out, err)


for s in solvers:
    print('{}:'.format(s))
    inp = inputs
    if re.match('cvc4-.*', s):
        print('\tAFP not supported (#5094)')
        print('\tSNRA not supported (#5109 / #5111)')
        inp = filter(lambda i: 'A' not in benchlogics[i] or 'FP' not in benchlogics[i], inp)
        inp = filter(lambda i: 'NRA' not in benchlogics[i] or 'S' not in benchlogics[i], inp)
    if re.match('mathsat-.*', s):
        print('\tDatatypes not supported')
        print('\tString not supported')
        print('\tTranscendentals not supported')
        inp = filter(lambda i: 'S' not in benchlogics[i], inp)
        inp = filter(lambda i: 'DT' not in benchlogics[i], inp)
        inp = filter(lambda i: 'T' not in benchlogics[i], inp)
    if re.match('smtinterpol-.*', s):
        print('\tBitvectors not supported')
        print('\tFloating-Point not supported')
        print('\tDatatypes not supported')
        print('\tString not supported')
        print('\tTranscendentals not supported')
        inp = filter(lambda i: 'BV' not in benchlogics[i], inp)
        inp = filter(lambda i: 'FP' not in benchlogics[i], inp)
        inp = filter(lambda i: 'S' not in benchlogics[i], inp)
        inp = filter(lambda i: 'DT' not in benchlogics[i], inp)
        inp = filter(lambda i: 'T' not in benchlogics[i], inp)

    for i in inp:
        start = time.time()
        out,err = run(solvers[s] + [i])
        dur = time.time() - start

        errs, result, out, err = status(s, out, err)
        if errs != [] or result is None:
            print('\t{}: {} ({:0.2f}s)'.format(i, result, dur))
            if errs != []:
                print('\t\t{}'.format('\n\t\t'.join(errs)))
            if err != '':
                print(err)
            if out != '':
                print(out)
