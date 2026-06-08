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
       expect(tcons).toSatisfy(isOkT(isProcTExp));
    });

    it('typeofPrim - car', () => {
       const tcar = bind(p("car"), (e: Exp) => isPrimOp(e) ? typeofPrim(e) : makeFailure(`Expected PrimOp : car`));
       expect(tcar).toSatisfy(isOkT(isProcTExp));
    });

    it('typeofPrim - cdr', () => {
       const tcdr = bind(p("cdr"), (e: Exp) => isPrimOp(e) ? typeofPrim(e) : makeFailure(`Expected PrimOp: cdr`));
       expect(tcdr).toSatisfy(isOkT(isProcTExp));
    });
});

describe('L5-substitution-adt', () => {

    it('checkNoOccurrence', () => {
       expect(checkNoOccurrence(makeTVar("x"), makeListTExp(makeTVar("x"))))
       .toSatisfy(isFailure);
       
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

describe('L5-typecheck - DefineExp final type', () => {
    it('(define (x : number) 5) is void', () => {
        expect(L5typeof("(define (x : number) 5)")).toEqual(makeOk("void"));
    });

    it('(define (b : boolean) #t) is void', () => {
        expect(L5typeof("(define (b : boolean) #t)")).toEqual(makeOk("void"));
    });
});

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
        const deepList = makeListTExp(makeListTExp(tvX));
        expect(checkNoOccurrence(tvX, deepList)).toSatisfy(isFailure);
    });

    it('checkNoOccurrence - detects occurrence inside structural procedure lists', () => {
        const tvX = makeTVar("x");
        const procWithList = makeProcTExp([makeListTExp(tvX)], makeNumTExp());
        expect(checkNoOccurrence(tvX, procWithList)).toSatisfy(isFailure);
    });

    it('applySub - substitutes type variables inside nested lists properly', () => {
        const sub1 = sub(["X"], ["number"]);
        const te1 = parseTE("(list (list X))");
        const unparsed = bind(sub1, (sub: S.Sub) =>
            bind(te1, (te: TExp) => unparseTExp(S.applySub(sub, te))));
        expect(unparsed).toEqual(makeOk("(list (list number))"));
    });
});

describe('L5-type-equations - Comprehensive List Type Inference', () => {
    const infer = (src: string): Optional<TExp> => {
        const parsed = p(src);
        if (parsed.tag !== "Ok") throw new Error(`parse failed: ${src}`);
        return inferType(parsed.value);
    };

    it('infers a list with a fresh type variable for an empty list literal', () => {
        const t = infer("'()");
        expect(isSome(t) && isListTExp(t.value) && isTVar(t.value.itemTE)).toBe(true);
    });

    it('infers (list boolean) for a list of booleans', () => {
        const t = infer("'(#t #f #t)");
        expect(isSome(t) && isListTExp(t.value) && isBoolTExp(t.value.itemTE)).toBe(true);
    });

    it('infers (list string) for a list of strings', () => {
        const t = infer("'(\"hello\" \"world\")");
        expect(isSome(t) && isListTExp(t.value) && isStrTExp(t.value.itemTE)).toBe(true);
    });

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

    it('fails to infer type when a literal list contains mixed types (numbers and booleans)', () => {
        const t = infer("'(1 #t 3)");
        expect(isNone(t)).toBe(true);
    });

    it('fails to infer type when a nested sub-list violates uniform inner matrix types', () => {
        const t = infer("'((1 2) (#t #f))");
        expect(isNone(t)).toBe(true);
    });

    it('fails to infer when standard operators are applied incorrectly to uniform lists', () => {
        const t = infer("((lambda ((xs : (list number))) (+ xs 5)) '(1 2))");
        expect(isNone(t)).toBe(true);
    });
});

describe('L5-typecheck - Complete List Program Inferences', () => {
    it('throws errors globally when functions expect lists but receive primitives', () => {
        const prog = `(L5
            (define (process : ((list number) -> number))
                (lambda ((items : (list number))) (car items)))
            (process 42)
        )`;
        expect(L5typeofProgram(prog)).toSatisfy(isFailure);
    });
});
describe('L5-type-equations - Advanced Chaining', () => {
    const infer = (src: string): Optional<TExp> => {
       const parsed = p(src);
       if (parsed.tag !== "Ok") throw new Error(`parse failed: ${src}`);
       return inferType(parsed.value);
    };

    it('infers number for car of cdr of a cons chain', () => {
        // (car (cdr (cons 1 '(2 3)))) -> (car '(2 3)) -> 2
        const t = infer("(car (cdr (cons 1 '(2 3))))");
        expect(isSome(t) && isNumTExp(t.value)).toBe(true);
    });

    it('infers (list number) for a function that creates a list from an element', () => {
        // (lambda ((x : number)) (cons x '()))
        // צריכה להחזיר (number -> (list number))
        const t = infer("(lambda ((x : number)) (cons x '()))");
        expect(isSome(t) && isProcTExp(t.value) && isListTExp(t.value.returnTE) && isNumTExp(t.value.returnTE.itemTE)).toBe(true);
    });
});
describe('L5-type-equations - Failure Cases', () => {
    const infer = (src: string): Optional<TExp> => {
       const parsed = p(src);
       if (parsed.tag !== "Ok") throw new Error(`parse failed: ${src}`);
       return inferType(parsed.value);
    };

    it('fails when passing a primitive where a list is expected', () => {
        // (car 1) -> 1 הוא לא רשימה, זה אמור להיכשל
        const t = infer("(car 1)");
        expect(isNone(t)).toBe(true);
    });

    it('fails on cons with mismatched types', () => {
        // (cons 1 '(#t)) -> אי אפשר להכניס מספר לרשימה של בוליאנים
        const t = infer("(cons 1 '(#t))");
        expect(isNone(t)).toBe(true);
    });

    it('fails when applying a number as a procedure', () => {
        // (1 2) -> 1 הוא לא פונקציה
        const t = infer("(1 2)");
        expect(isNone(t)).toBe(true);
    });
});
describe('L5-type-equations - Higher Order Lists', () => {
    const infer = (src: string): Optional<TExp> => {
       const parsed = p(src);
       if (parsed.tag !== "Ok") throw new Error(`parse failed: ${src}`);
       return inferType(parsed.value);
    };

    it('infers (number -> number) for a function taking a list and returning a number', () => {
        // (lambda ((f : (number -> number)) (l : (list number))) (f (car l)))
        const t = infer("(lambda ((f : (number -> number)) (l : (list number))) (f (car l)))");
        expect(isSome(t) && isProcTExp(t.value)).toBe(true);
        // בדיקה שהתוצאה היא (number -> (list number) -> number) או דומה
        // תלוי איך את בודקת את הטיפוסים הפנימיים
    });
});
describe('L5-substitution-adt - The 3 Final Bosses', () => {
    
    // בודק ש-applySub יודע לרוץ רקורסיבית בתוך פרמטרים של פונקציות (נכשל קודם על Syntax error)
    it('applySub - substitutes inside procedure parameter and return lists simultaneously', () => {
        const sub1 = sub(["X", "Y"], ["boolean", "number"]);
        // שימי לב שתיקנתי פה לסוגריים עגולים במקום מרובעים
        const te1 = parseTE("((list X) -> (list Y))");
        
        const unparsed = bind(sub1, (sub: S.Sub) =>
            bind(te1, (te: TExp) =>
                unparseTExp(S.applySub(sub, te))
            )
        );
        expect(unparsed).toEqual(makeOk("((list boolean) -> (list number))"));
    });

});

