#!/usr/bin/env python2.7
import sympy
import z3
import numpy as np
import scipy.optimize as op
import argparse
import sys, os
import time
import collections
import subprocess
import multiprocessing as mp
import warnings
import struct
import cPickle as pickle

sys.path.insert(0,os.path.join(os.getcwd(),"build/R_ulp"))
import foo 
reload(foo) #necessary because name 'foo' now still points to foo_square

def str2bool(v):
    if v.lower() in ('yes', 'true', 't', 'y', '1'):
        return True
    elif v.lower() in ('no', 'false', 'f', 'n', '0'):
        return False
    else:
        raise argparse.ArgumentTypeError('Boolean value expected.')

def noop_min(fun, x0, args, **options):
    return op.OptimizeResult(x=x0, fun=fun(x0), success=True, nfev=1)


class Sort:
    UNKNOWN='unknown'
    Float32 = 'float32'
    Float64 = 'float64'
    Real='real'
    Int='int'


def _is_true(a):
    return a.decl().kind()==z3.Z3_OP_TRUE


def replace_all(text, dic):
    for i, j in dic.iteritems():
        text = text.replace(i, j)
    return text


def rename_var(var):
    reps = {':':'_', '@':'_', '|':'_',"#":'_',"!":"_"}
    return replace_all(var,reps)


def verify_solution(ez, X_star,symbolTable,printModel=False):
    assert isinstance(symbolTable, collections.OrderedDict)
    assert isinstance(ez, z3.ExprRef)
    assert len(symbolTable)==X_star.size
    model=[]
    # (sympy.Symbol('x'), 
    for (s,val) in zip(symbolTable.items(), X_star): 
        var, sort = s[0],s[1]
        var=rename_var(var)
        
        if sort == Sort.Float32:
            var_z3=z3.FP(str(var),z3.Float32())
            val_z3=z3.FPVal(val,z3.Float32())
        elif sort == Sort.Float64:
            var_z3=z3.FP(str(var),z3.Float64())
            val_z3=z3.FPVal(val,z3.Float64())
        else:
            raise NotImplementedError("Unexpected type %s" %sort)            
        model.append((var_z3,val_z3))
    if printModel:
        print "model: "
        print model
    return _is_true(z3.simplify(z3.substitute(ez, *model)))

    
def _getSort(expr_z3):
    assert isinstance(expr_z3, z3.ExprRef)
    if expr_z3.sort()==z3.Float32():
        return Sort.Float32
    if expr_z3.sort()==z3.Float64():
        return Sort.Float64
    if expr_z3.sort()==z3.RealSort():
        return Sort.Real
    if expr_z3.sort()==z3.IntSort():
        return Sort.Int
    return Sort. UNKNOWN 

##
def var_hash(expr_z3):
    return "_x_"+expr_z3.hash()

foundit=mp.Event()
def _callback_global(x,f,accepted):
    #    print("at minimum %.4f  %s" % (f, 'accepted' if (accepted) else 'not accepted'))
    if f==0 or foundit.is_set():
        foundit.set()
        return True

def scale(X,i):
    return  X**(2*i+1)

    
def R_quick(X,i,f):
    return f(* scale(X,i))


def mcmc_bis(i):
    print "*******value of i = ",i

    
def mcmc(args,i):
    np.random.seed()
    t_start_round1=time.time()
    if args.method=='noop_min': _minimizer_kwargs=dict(method=noop_min)
    else: _minimizer_kwargs=dict(method=args.method)
    sp=np.zeros(foo.dim)+args.startPoint+i

    res= op.basinhopping(lambda X: R_quick(X,i,foo.R),sp,niter=args.niter,stepsize=args.stepSize, minimizer_kwargs=_minimizer_kwargs,callback=_callback_global)
    if args.showResult: print "result (round 1) with i = ",i,":", '\n', res, '\n'

    # do some change here. If the first round gives a good/bad enough result, no need for the second. 
    X_star=scale(res.x,i)
    R_star=res.fun
    
    if res.fun!=0 and res.fun<args.round2_threshold:
        if args.showTime: print "[Xsat] round2_move"
        sp=np.array([res.x+0]) if res.x.ndim==0 else res.x
        obj_near=lambda N:foo.R(* nth_fp_vectorized(N, scale(sp,i)))

        res_round2 = op.basinhopping(obj_near,np.zeros(foo.dim),niter=args.round2_niter,stepsize=args.round2_stepsize,minimizer_kwargs=_minimizer_kwargs,callback=_callback_global)
        if args.showResult: print "result (round 2) with i = ",i, '\n', res_round2, '\n'

        R_star=res_round2.fun
        ##change this because I could have used the R_quick.
        X_star= nth_fp_vectorized(res_round2.x,scale(sp,i))
    return (X_star,R_star)


#little-endian!!!!!!!!!!!!!!
@np.vectorize
def nth_fp_vectorized(n, x):
    if x<0: return -nth_fp_vectorized(-n,-x)
    n=int(n)
    s = struct.pack('<d', x)
    i = struct.unpack('<Q', s)[0]
    m =	i + n
    #m = n + struct.unpack('!i',struct.pack('!f',x))[0]
    if m < 0:
        sign_bit = 0x8000000000000000
        m = -m
    else:
        sign_bit = 0
    if m >= 0x7ff0000000000000:
        warnings.warn("Value out of range, with n= %g,x=%g,m=%g, process=%g" %(n,x,m, mp.current_process.name))
        m=0x7ff0000000000000
#        raise ValueError('out of range')
    bit_pattern = struct.pack('Q', m | sign_bit)
    return struct.unpack('d', bit_pattern)[0]


def nth_fp_vectorized2(N,X):
    return np.vectorize(nth_fp)(N,X)


def scales():
    return [(lambda x:x**11, lambda x: np.sign(x)* np.abs(x)**(1.0/11)), \
            (lambda x:x**17, lambda x: np.sign(x)*np.abs(x)**(1.0/17)),\
            (lambda x: x**25,lambda x:np.sign(x)*np.abs(x)**(1.0/25)) \
    ]

#to handle an issue due to 'powell': it returns a zero-dimensional array even if the starting point is of one dimension.         
def tr_help(X):
        if X.ndim==0: return np.array([X])
        else: return X


#execute it quickly, since a lock is set
def log_result(result):
    (X_star,R_star)=result
    if args.showTime: print "[Xsat-multi] ENTERING: ",mp.current_process().name,  "log_result Minimum=", R_star
    assert len(results_pool)<=1
    if len(results_pool)==0:
        results_pool.append(result)
    else:
        (X_star_pool,R_star_pool)=results_pool[0]                
        if R_star<R_star_pool:
            results_pool[0]=result
            if R_star_pool==0:
                if args.showTime: print "[Xsat-multi] I kill the other process now!!!"
                pool.terminate()
            

if __name__ == "__main__":
    timeStamp0=time.time()

    parser = argparse.ArgumentParser(prog='Xsat')
#    parser.add_argument('smt2_file', help='specify the smt2 file to analyze.',type=argparse.FileType('r'))
    parser.add_argument('-v', '--version', action='version', version='%(prog) version 12/18/2015')
    parser.add_argument ('--niter', help='niter in basinhopping', action='store', type=int, required=False,default=100)
    parser.add_argument ('--nStartOver', help='startOver times', action='store', type=int, required=False,default=2)
    parser.add_argument('--method', help='Local minimization procedure',  default='powell', choices=['powell', 'slsqp', 'cg',  'l-bfgs-b', 'cobyla','tnc',  'bfgs', 'nelder-mead','noop_min']
  )
    parser.add_argument ('--showTime', help='show the time-related info (default: false)', action='store_true', default=False)
    parser.add_argument ('--showResult', help='show the basinhopping output (default:false)', action='store_true',default=False)
    parser.add_argument ('--stepSize', help='parameter of basinhopping', type=float, default=10.0);
    parser.add_argument ('--round2_stepsize', help='parameter of basinhopping', type=float, default=100.0);        
    parser.add_argument ('--verify', help='verify the model', action='store_true',default=False)
    parser.add_argument ('--showModel', help='show the model as a var->value mapping', action='store_true',default=False)
    parser.add_argument ('--showSymbolTable', help='show the symbol table, var->type', action='store_true',default=False)
    parser.add_argument ('--showConstraint', help='show the constraint, using the Z3 frontend', action='store_true',default=False)
    parser.add_argument ('--showVariableNumber', help='show variable number, using the Z3 frontend', action='store_true',default=False)

    parser.add_argument('--command_compilation', help='the command used to compile the generated foo.c to foo.so', default='gcc -O3 -fbracket-depth=2048 -fPIC -I /usr/local/Cellar/python/2.7.9/Frameworks/Python.framework/Versions/2.7/include/python2.7/ %(file)s.c -dynamiclib -o %(file)s.so -L /usr/local/Cellar/python/2.7.9/Frameworks/Python.framework/Versions/Current/lib/ -lpython2.7')
    parser.add_argument ('--startPoint', help='start point in a single dimension', action='store',type=float,default=1.0);
    parser.add_argument ('--round2_threshold', help='threshold_low for round2', action='store',type=float,default=1e9);
    parser.add_argument ('--round3_threshold', help='threshold  for round3', action='store',type=float,default=1e10);
    parser.add_argument("--multi", help="multi-processing (default: true)",default=True,action='store', type=str2bool)
#    parser.add_argument("--single", help="single processor  (default: true)",default=True,action='store')

    #parser.add_argument("--round2", help="activate round2 when unsat (default: false)",default=False,action='store_true')
    parser.add_argument("--round2_niter", help="niter for round2",action='store',type=int,required=False,default=50)
    parser.add_argument("--round3_niter", help="niter for round3",action='store',type=int,required=False,default=1000)
    parser.add_argument("--round3_stepsize", help="stepsize for round3",action='store',type=float,required=False,default=5.0)
        
    parser.add_argument("--suppressWarning", help="Suppress warnings",default=False,action='store_true')
    parser.add_argument("--debug", help="debug mode (with verify and showresults, etc.)",default=True,action='store_true')
    parser.add_argument("--printModel", help="print the model",default=False, action='store_true')
    parser.add_argument("--bench", help="benchmarking mode",default=False, action='store_true')
    parser.add_argument("--genOnly", help="generate code only, without deciding satisfiability",default=False,action='store_true')
    
    args = parser.parse_args()            
        
    if args.bench:
        args.debug=False
        args.verify=False
        args.showResult=False
        args.showTime=False
        args.suppressWarning=True
        args.multi=True

    if args.debug:
        args.verify=True
        args.showResult=True
        args.showTime=True
        args.suppressWarning=False

    t_start=time.time()

    if args.suppressWarning:
        warnings.filterwarnings("ignore")

    with open ("build/foo.symbolTable","rb") as f:
        symbolTable=pickle.load(f)
    if len(symbolTable)==0:
        print "sat"
        sys.exit(0)

    if args.multi:
        if args.showTime: print "[Xsat] ENTERING: main_multi"
        results_pool=[]
        result_mult=None
        pool = mp.Pool()

        for i in range(mp.cpu_count()):
            p=pool.apply_async(mcmc, args=(args, i,  ), callback=log_result)
        pool.close()
        pool.join()
        
        assert len(results_pool)==1
        (X_star,R_star)=results_pool[0]
        if X_star.ndim==0: X_star=np.array([X_star[()]])
    
        if R_star==0: print 'sat'
        else: print 'unsat'     

        if args.showResult:
            print "X_star (final)", X_star
            print "R_star (final)", R_star

    t_mcmc=time.time()

    if args.verify:
        if args.showTime: print "[Xsat] verify X_star with z3 front-end"        
        with open ("XSAT_IN.txt") as f:
            try: expr_z3=z3.simplify(z3.parse_smt2_file(f.read().rstrip()))
            except z3.Z3Exception: sys.stderr.write("[Xsat] The Z3 fornt-end fails when verifying the model.\n")
        verified = verify_solution(expr_z3,X_star, symbolTable,printModel=args.printModel)
        if verified and R_star!=0: sys.stderr.write("WARNING!!!!!!!!!!!!!!!! Actually sat.\n")
        elif not verified and R_star==0: sys.stderr.write("WARNING!!!!!!!!!!!!!!!  Wrong model !\n")
        
    t_verify=time.time()
    
    if args.showSymbolTable:
        print symbolTable
    if args.showConstraint: print expr_z3
    if args.showVariableNumber: print "nVar = ", len(symbolTable)
    
    if args.showTime:
        print "[Xsat] Time elapsed:"
#        print "  parse_and_compile    : %g seconds " % (t_parse_and_compile-t_start)
        print "  solve (all)  : %g seconds" % (t_mcmc-t_start)
        if not args.multi:
            print "        round1  : %g seconds" % (t_round1_end-t_round1_start)
            print "        round2  : %g seconds" % (t_round2_end-t_round2_start)
            print "        round3  : %g seconds" % (t_round3_end-t_round3_start)
            print "        verification after round1 also takes a little time"
        print "  verify : %g seconds" %(t_verify -t_mcmc)
        print "\n  Total        : %g seconds" %(t_verify - t_start)
