import { isNumExp, isBoolExp, isVarRef, isPrimOp, isProgram, isDefineExp, isVarDecl,
    isAppExp, isStrExp, isIfExp, isProcExp, isLetExp, isLitExp, isLetrecExp, isSetExp,
    parseL5Exp, unparse, Exp, parseL5, 
    Program} from "../../src/L5/L5-ast";
import { Result, bind, isFailure, isOk, isOkT, makeFailure, makeOk, mapv } from "../../src/shared/result";
import { applyTEnv, makeEmptyTEnv, makeExtendTEnv, TEnv } from "../../src/L5/TEnv";
import { parse as parseSexp } from "../../src/shared/parser";
import { typeofPrim, typeofExp, typeofProgram } from "../../src/L5/L5-typecheck";
import { isBoolTExp, isListTExp, isNumTExp, isProcTExp, isStrTExp, isTVar, makeListTExp, makeNumTExp, makeProcTExp, makeTVar, parseTE, parseTExp, TExp, unparseTExp } from "../../src/L5/TExp";
import { checkNoOccurrence } from "../../src/L5/L5-substitution-adt";
import * as S from "../../src/L5/L5-substitution-adt";
import { inferType } from "../../src/L5/L5-type-equations";
import { isNone, isSome, Optional } from "../../src/shared/optional";
import { sub } from "./test-helpers";

const p = (x: string): Result<Exp> => bind(parseSexp(x), parseL5Exp);

export const L5typeofProgram = (concreteExp: string): Result<string> =>
    bind(parseL5(concreteExp), (e: Program) =>
        bind(typeofProgram(e, makeEmptyTEnv()), unparseTExp));

export const L5typeof = (concreteExp: string): Result<string> =>
    bind(p(concreteExp), (e: Exp) => 
            bind(typeofExp(e, makeEmptyTEnv()), unparseTExp));
describe('L5-typecheck', () => {

it('typeofPrim - cons', () => {
   const tcons = bind(p("cons"), (e: Exp) => isPrimOp(e) ? typeofPrim(e) : makeFailure(`Expected PrimOp: cons`));

   // cons is ProcTExp
   expect(tcons).toSatisfy(isOkT(isProcTExp));
   
   // cons is ProcTExp with 2 parameters
   expect(bind(tcons, (x) =>
       isProcTExp(x)
       ? makeOk(x.paramTEs.length)
       : makeFailure("not ProcTExp")
       )).toEqual(makeOk(2));
});

it('typeofPrim - car', () => {
   const tcar = bind(p("car"), (e: Exp) => isPrimOp(e) ? typeofPrim(e) : makeFailure(`Expected PrimOp : car`));

   // car is ProcTExp
   expect(tcar).toSatisfy(isOkT(isProcTExp));
   
   // car is ProcTExp with 2 parameters
   expect(bind(tcar, (x) =>
       isProcTExp(x)
       ? makeOk(x.paramTEs.length)
       : makeFailure("not ProcTExp")
       )).toEqual(makeOk(1));

});

it('typeofPrim - cdr', () => {
   const tcdr = bind(p("cdr"), (e: Exp) => isPrimOp(e) ? typeofPrim(e) : makeFailure(`Expected PrimOp: cdr`));

   // cdr is ProcTExp
   expect(tcdr).toSatisfy(isOkT(isProcTExp));
   
   // cdr is ProcTExp with 2 parameters
   expect(bind(tcdr, (x) =>
       isProcTExp(x)
       ? makeOk(x.paramTEs.length)
       : makeFailure("not ProcTExp")
       )).toEqual(makeOk(1));

});
});

describe('L5-substitution-adt', () => {

it('checkNoOccurrence', () => {

   // type variable occurs in a list of itself
   expect(checkNoOccurrence(makeTVar("x"), makeListTExp(makeTVar("x"))))
   .toSatisfy(isFailure);
   
   // type variable doesn't occur in a list of another type variable
   expect(checkNoOccurrence(makeTVar("x"), makeListTExp(makeTVar("y"))))
   .toEqual(makeOk(true));
});

it('applySub - single subtitution', () => {
   const sub1 = sub(["X"], ["boolean"]);
   const texp = "(list X)";
   const te1 = parseTE(texp);
   const unparsed = bind(sub1, (sub: S.Sub) =>
                       bind(te1, (te: TExp) =>
                           unparseTExp(S.applySub(sub, te))));
   expect(unparsed).toEqual(makeOk("(list boolean)"));
});

});

describe('L5-typecheck - define', () => {
it('should correctly type a boolean definition', () => {
   expect(L5typeof("(define (x : boolean) (if (> 1 2) #t #f))")).toEqual(makeOk("void"));
});

it('should correctly type a number definition', () => {
   expect(L5typeof("(define (x : number) 5)")).toEqual(makeOk("void"));
});
});

describe('L5-typecheck - program type', () => {
it('should correctly type a simple program with number', () => {
   expect(L5typeofProgram("(L5 (define (x : number) 5) (+ x 1))")).toEqual(makeOk("number"));
});

it('should correctly type a simple program with boolean', () => {
   expect(L5typeofProgram("(L5 (define (x : boolean) #t) x)")).toEqual(makeOk("boolean"));
});
});

describe('L5-type-equations - list inference', () => {
// Drive `inferType` directly. `verifyTeOfExprWithEquations` relies on
// `equivalentTEs`, which does not recurse into ListTExp, so we structurally
// check the inferred TExp instead.
const infer = (src: string): Optional<TExp> => {
   const parsed = p(src);
   if (parsed.tag !== "Ok") throw new Error(`parse failed: ${src}`);
   return inferType(parsed.value);
};
it('infers (list number) for cons of number into list literal via lambda app', () => {
    const t = infer("((lambda ((xs : (list number))) (cons 0 xs)) '(1 2 3))");
    expect(isSome(t) && isListTExp(t.value) && isNumTExp(t.value.itemTE)).toBe(true);
});
it('infers number for car of list number', () => {
    const t = infer("((lambda ((xs : (list number))) (car xs)) '(1 2 3))");
    expect(isSome(t) && isNumTExp(t.value)).toBe(true);
});

});

// ------------------------------------------------------------
// L5-typecheck - DefineExp final type (always "void" when well-typed)
// ------------------------------------------------------------
describe('L5-typecheck - DefineExp final type', () => {

    it('(define (x : number) 5) is void', () => {
        expect(L5typeof("(define (x : number) 5)")).toEqual(makeOk("void"));
    });

    it('(define (b : boolean) #t) is void', () => {
        expect(L5typeof("(define (b : boolean) #t)")).toEqual(makeOk("void"));
    });
});

// ------------------------------------------------------------
// L5-typecheck - Program final return type
// ------------------------------------------------------------
describe('L5-typecheck - Program final return type', () => {

    it('(L5 5) returns number', () => {
        expect(L5typeofProgram("(L5 5)")).toEqual(makeOk("number"));
    });

    it('(L5 (define (x : number) 5) (+ x 1)) returns number', () => {
        expect(L5typeofProgram("(L5 (define (x : number) 5) (+ x 1))"))
            .toEqual(makeOk("number"));
    });
});

describe('L5-substitution-adt - Deep List Constraints', () => {

    it('checkNoOccurrence - detects deep occurrence inside nested lists', () => {
        const tvX = makeTVar("x");
        // Deep nested type: (list (list x))
        const deepList = makeListTExp(makeListTExp(tvX));
        
        expect(checkNoOccurrence(tvX, deepList)).toSatisfy(isFailure);
    });

    it('checkNoOccurrence - detects occurrence inside structural procedure lists', () => {
        const tvX = makeTVar("x");
        // Compound type: [ (list x) -> number ]
        const procWithList = makeProcTExp([makeListTExp(tvX)], makeNumTExp());
        
        expect(checkNoOccurrence(tvX, procWithList)).toSatisfy(isFailure);
    });

    it('applySub - substitutes type variables inside nested lists properly', () => {
        const sub1 = sub(["X"], ["number"]);
        const te1 = parseTE("(list (list X))");
        
        const unparsed = bind(sub1, (sub: S.Sub) =>
            bind(te1, (te: TExp) =>
                unparseTExp(S.applySub(sub, te))
            )
        );
        expect(unparsed).toEqual(makeOk("(list (list number))"));
    });

    it('applySub - substitutes inside procedure parameter and return lists simultaneously', () => {
        const sub1 = sub(["X", "Y"], ["boolean", "number"]);
        const te1 = parseTE("[(list X) -> (list Y)]");
        
        const unparsed = bind(sub1, (sub: S.Sub) =>
            bind(te1, (te: TExp) =>
                unparseTExp(S.applySub(sub, te))
            )
        );
        expect(unparsed).toEqual(makeOk("[(list boolean) -> (list number)]"));
    });
});

describe('L5-type-equations - Comprehensive List Type Inference', () => {

    const infer = (src: string): Optional<TExp> => {
        const parsed = p(src);
        if (parsed.tag !== "Ok") throw new Error(`parse failed: ${src}`);
        return inferType(parsed.value);
    };

    // --- Empty Lists ---
    it('infers a list with a fresh type variable for an empty list literal', () => {
        const t = infer("'()");
        expect(isSome(t) && isListTExp(t.value) && isTVar(t.value.itemTE)).toBe(true);
    });

    // --- Primitive Lists ---
    it('infers (list boolean) for a list of booleans', () => {
        const t = infer("'(#t #f #t)");
        expect(isSome(t) && isListTExp(t.value) && isBoolTExp(t.value.itemTE)).toBe(true);
    });

    it('infers (list string) for a list of strings', () => {
        const t = infer("'(\"hello\" \"world\")");
        expect(isSome(t) && isListTExp(t.value) && isStrTExp(t.value.itemTE)).toBe(true);
    });

    // --- Nested Compound Structures ---
    it('infers (list (list number)) for nested numerical lists', () => {
        const t = infer("'((1 2) (3 4))");
        expect(isSome(t) && isListTExp(t.value)).toBe(true);
        
        const innerType = (t as any).value.itemTE;
        expect(isListTExp(innerType) && isNumTExp(innerType.itemTE)).toBe(true);
    });

    it('infers (list (list (list boolean))) for deeply nested structures', () => {
        const t = infer("'(((#t)))");
        expect(isSome(t) && isListTExp(t.value)).toBe(true);
        const level2 = (t as any).value.itemTE;
        expect(isListTExp(level2)).toBe(true);
        const level3 = level2.itemTE;
        expect(isListTExp(level3) && isBoolTExp(level3.itemTE)).toBe(true);
    });

    // --- Operations, Car, Cdr & Lambda applications ---
    it('infers (list number) when fetching the cdr of a nested matrix list', () => {
        const t = infer("((lambda ((xs : (list (list number)))) (cdr xs)) '((1 2) (3 4)))");
        expect(isSome(t) && isListTExp(t.value)).toBe(true);
        const itemType = (t as any).value.itemTE;
        expect(isListTExp(itemType) && isNumTExp(itemType.itemTE)).toBe(true);
    });

    it('infers a boolean from checking the head of a boolean list application', () => {
        const t = infer("((lambda ((xs : (list boolean))) (car xs)) '(#f #t))");
        expect(isSome(t) && isBoolTExp(t.value)).toBe(true);
    });

    it('infers (list number) when consing a number onto an empty list parameter', () => {
        const t = infer("((lambda ((xs : (list number))) (cons 42 xs)) '())");
        expect(isSome(t) && isListTExp(t.value) && isNumTExp(t.value.itemTE)).toBe(true);
    });

    // --- Structural Verification & Homogeneity Errors ---
    it('fails to infer type when a literal list contains mixed types (numbers and booleans)', () => {
        // This should safely trigger a unification failure because number !== boolean
        const t = infer("'(1 #t 3)");
        expect(isNone(t)).toBe(true);
    });

    it('fails to infer type when a nested sub-list violates uniform inner matrix types', () => {
        // Outer expects elements of type (list number). The second element is a (list boolean).
        const t = infer("'((1 2) (#t #f))");
        expect(isNone(t)).toBe(true);
    });

    it('fails to infer when standard operators are applied incorrectly to uniform lists', () => {
        // Pass a list instead of a number into an arithmetic addition procedure application
        const t = infer("((lambda ((xs : (list number))) (+ xs 5)) '(1 2))");
        expect(isNone(t)).toBe(true);
    });
});

describe('L5-typecheck - Complete List Program Inferences', () => {

    it('properly asserts primitive list parameters inside bound definitions', () => {
        const prog = `(L5 
            (define (filter-nums : ((list number) -> (list number))) 
                (lambda ((items : (list number))) (cdr items)))
            (filter-nums '(10 20 30))
        )`;
        expect(L5typeofProgram(prog)).toEqual(makeOk("(list number)"));
    });

    it('verifies complex compound execution yielding primitive boolean values', () => {
        const prog = `(L5
            (define (is-first-true? : ((list boolean) -> boolean))
                (lambda ((flags : (list boolean))) (car flags)))
            (is-first-true? '(#t #f #f))
        )`;
        expect(L5typeofProgram(prog)).toEqual(makeOk("boolean"));
    });

    it('throws errors globally when functions expect lists but receive primitives', () => {
        const prog = `(L5
            (define (process : ((list number) -> number))
                (lambda ((items : (list number))) (car items)))
            (process 42)
        )`;
        expect(L5typeofProgram(prog)).toSatisfy(isFailure);
    });
});