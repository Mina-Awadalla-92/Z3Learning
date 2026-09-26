using Microsoft.Z3;

public static class Z3Learning
{
    private static readonly Action[] Lessons =
    [
        Lesson1_SatVsUnsat,
        Lesson2_ProveByRefutation,
        Lesson3_BranchesWithIte,
        Lesson4_SymbolicExecutor,
        Lesson5_MinMax,
    ];

    public static void Main(string[] args)
    {
        var toRun = args.Length > 0 ? [Lessons[int.Parse(args[0]) - 1]] : Lessons;
        foreach (var lesson in toRun) { lesson(); Console.WriteLine("\n"); }
    }

    // Lesson 1: sat vs unsat 
    public static void Lesson1_SatVsUnsat()
    {
        Console.WriteLine($"=== Lesson 1: sat vs unsat ===\n");

        using var ctx = new Context();
        var x = ctx.MkIntConst("x"); // a symbolic integer some unknown int called x
        var y = ctx.MkIntConst("y");

        var s = ctx.MkSolver();
        s.Assert(ctx.MkEq(ctx.MkAdd(x, y), ctx.MkInt(10)));
        s.Assert(ctx.MkEq(ctx.MkSub(x, y), ctx.MkInt(4)));

        var status = s.Check();
        Console.WriteLine($"x + y == 10, x - y == 4  ->  {status}");
        if (status == Status.SATISFIABLE)
            Console.WriteLine($"  a solution Z3 found: {s.Model}"); 

        // Now make it impossible:
        var s2 = ctx.MkSolver();
        s2.Assert(ctx.MkEq(x, ctx.MkInt(5)));
        s2.Assert(ctx.MkEq(x, ctx.MkInt(6)));
        Console.WriteLine($"\nx == 5 AND x == 6        ->  {s2.Check()}  (no model — contradiction)");
    }

    // Lesson 2: proving something is ALWAYS true, by trying to disprove it
    public static void Lesson2_ProveByRefutation()
    {
        Console.WriteLine($"=== Lesson 2: prove-by-refutation ===\n");
        Console.WriteLine("To prove A always equals B, assert NOT(A == B) and check.");
        Console.WriteLine("  unsat -> no counterexample exists -> A and B are always equal");
        Console.WriteLine("  sat   -> Z3 just handed you a counterexample -> Not equivalent\n");

        using var ctx = new Context();
        var r = ctx.MkRealConst("r"); // a real number symbolic input

        // Two programs computing circle area two different but equal ways:
        var pi = ctx.MkReal(31415926, 10000000);   // rational approximation of pi
        var original  = ctx.MkMul(pi, r, r);      
        var generated = ctx.MkMul(r, r, pi);      

        Prove(ctx, "pi*r*r  vs  r*r*pi", original, generated);

        var buggy = ctx.MkMul(ctx.MkReal(2), pi, r); // circumference
        Prove(ctx, "pi*r*r  vs  2*pi*r", original, buggy);
    }

    // Lesson 3: if/else via MkITE 
    public static void Lesson3_BranchesWithIte()
    {
        Console.WriteLine($"=== Lesson 3: modeling if/else with ITE (If-Then-Else) ===\n");

        using var ctx = new Context();
        var x = ctx.MkRealConst("x");

        var cond = ctx.MkGt(x, ctx.MkReal(0)); // x > 0
        var y = (ArithExpr)ctx.MkITE(cond, x, ctx.MkUnaryMinus(x)); // y = (x > 0) ? x : -x

        // Prove y is never negative. Ask for a negative y and expect unsat.
        var solver = ctx.MkSolver();
        solver.Assert(ctx.MkLt(y, ctx.MkReal(0)));
        Console.WriteLine($"can ITE(x>0, x, -x) ever be negative?  ->  {solver.Check()}  (unsat = never)");

        // Compare against a buggy translation that forgot the negation:
        var buggyY = (ArithExpr)ctx.MkITE(cond, x, x); 
        Console.WriteLine();
        Prove(ctx, "correct abs()  vs  buggy translation", y, buggyY);
    }

    // Lesson 4: a tiny SymbolicExecutor
    public static void Lesson4_SymbolicExecutor()
    {
        Console.WriteLine($"=== Lesson 4: mini symbolic executor ===\n");
        Console.WriteLine("  if (speed > limit) result = limit;");
        Console.WriteLine("  else result = speed;");
        Console.WriteLine("  result = result * scale;\n");

        using var ctx = new Context();
        var speed = ctx.MkRealConst("speed");
        var limit = ctx.MkRealConst("limit");
        var scale = ctx.MkRealConst("scale");

        var state = new Dictionary<string, ArithExpr>
        {
            ["speed"] = speed,
            ["limit"] = limit,
            ["scale"] = scale,
        };

        // if (speed > limit) { result = limit; } else { result = speed; }
        var cond = ctx.MkGt(speed, limit);
        var thenState = new Dictionary<string, ArithExpr>(state) { ["result"] = limit };
        var elseState = new Dictionary<string, ArithExpr>(state) { ["result"] = speed };
        state["result"] = (ArithExpr)ctx.MkITE(cond, thenState["result"], elseState["result"]);

        state["result"] = ctx.MkMul(state["result"], scale);

        Console.WriteLine("  Z3 says:  " + state["result"].Simplify());
        Console.WriteLine("  In C#:    scale * (speed <= limit ? speed : limit)");
        Console.WriteLine("  Simplify() just rewrote our speed > limit condition into an equivalent speed <= limit with the branches swapped.");

        // Prove a property: result never exceeds limit*scale (assuming scale >= 0).
        var solver = ctx.MkSolver();
        solver.Assert(ctx.MkGe(scale, ctx.MkReal(0)));   // assumption  scale >= 0
        // to prove result never exceeds limit * scale, try prove violation  result > limit * scale
        solver.Assert(ctx.MkGt(state["result"], ctx.MkMul(limit, scale)));     
        Console.WriteLine($"\ncan result exceed limit*scale (scale>=0)?  ->  {solver.Check()} ");
    }

    // Lesson 5: The Min Max 
    public static void Lesson5_MinMax()
    {
        Console.WriteLine($"=== Lesson 5: The Min Max ===\n");
        Console.WriteLine("ExpressionLowerer gives Min/Max an actual ITE definition");

        using var ctx = new Context();
        var a = ctx.MkRealConst("a");
        var b = ctx.MkRealConst("b");

        // sorting is encoded in the two local functions
        ArithExpr Min(ArithExpr x, ArithExpr y) => (ArithExpr)ctx.MkITE(ctx.MkLe(x, y), x, y);
        ArithExpr Max(ArithExpr x, ArithExpr y) => (ArithExpr)ctx.MkITE(ctx.MkGe(x, y), x, y);

        // original code: emit pair as (Min(a,b), Max(a,b))
        var originalLow  = Min(a, b);
        var originalHigh = Max(a, b);

        // buggy generated code: hardcoded (a, b) with no sorting
        var generatedLow  = a;
        var generatedHigh = b;

        // Two outputs to compare -> some output differs = OR of the two inequalities.
        var solver = ctx.MkSolver();
        solver.Assert(ctx.MkOr(
            ctx.MkNot(ctx.MkEq(originalLow, generatedLow)),
            ctx.MkNot(ctx.MkEq(originalHigh, generatedHigh))));

        var status = solver.Check();
        Console.WriteLine($"(Min(a,b), Max(a,b))  vs  (a, b) unsorted  ->  {status}");
        if (status == Status.SATISFIABLE)
            Console.WriteLine($"  counterexample (this is the a > b case): {solver.Model}");
    }

    /// <summary>
    /// Method to check if a and b are equal for all inputs
    /// Asserts NOT(a == b): unsat means proved equal, sat means Z3 found a counterexample.
    /// </summary>
    private static Status Prove(Context ctx, string label, Expr a, Expr b)
    {
        var solver = ctx.MkSolver();
        solver.Assert(ctx.MkNot(ctx.MkEq(a, b)));
        var status = solver.Check();

        Console.WriteLine($"{label}  ->  {status}");
        Console.WriteLine(status switch
        {
            Status.UNSATISFIABLE => "  => PROVED equivalent for every possible input.",
            Status.SATISFIABLE   => $"  => NOT equivalent. counterexample: {solver.Model}",
            _                    => $"  => Z3 gave up: {solver.ReasonUnknown}",
        });
        return status;
    }

}
