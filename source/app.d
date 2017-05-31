module appx;
import lambdanorm.expr;
import std.stdio;

void main() {
  auto a = ident("a"),
       b = ident("b"),
       f = ident("f"),
       n = ident("n"),
       p = ident("p"),
       q = ident("q"),
       x = ident("x"),
       y = ident("y"),
       z = ident("z");

  auto zero = abst(f, abst(x, x)),
       one = abst(f, abst(x, app(f, x))),
       two = abst(f, abst(x, app(f, app(f, x)))),
       three = abst(f, abst(x, app(f, app(f, app(f, x)))));

  writeln("zero  := ", zero.stringof);
  writeln("one   := ", one.stringof);
  writeln("two   := ", two.stringof);
  writeln("three := ", three.stringof);

  auto _true  = abst(a, abst(b, a)),
       _false = abst(a, abst(b, b)),
       _if    = abst(f, abst(x, abst(y, app(app(f, x), y))));

  writeln("_true  := ", _true.stringof);
  writeln("_false := ", _false.stringof);
  writeln("_if    := ", _if.stringof);

  writeln("app(app(app(_if, _true), p), q).stringof -> ", app(app(app(_if, _true), p), q).stringof);
  writeln("app(app(app(_if, _true),  p), q).normalize.isEqualExpr(p) -> ", app(app(app(_if, _true),  p), q).normalize.isEqualExpr(p));
  writeln("app(app(app(_if, _false), p), q).normalize.isEqualExpr(q) -> ", app(app(app(_if, _false), p), q).normalize.isEqualExpr(q));

  auto isZero = abst(n, app(app(n, abst(y, _false)), _true));
  writeln("isZero := ", isZero.stringof);
  writeln("app(isZero, zero).isEqualExpr(_true) -> ", app(isZero, zero).normalize.isEqualExpr(_true));
  writeln("app(isZero, one).isEqualExpr(_false) -> ", app(isZero, one).normalize.isEqualExpr(_false));

  auto cons = abst(x, abst(y, abst(z, app(app(z, x), y)))),
       car  = abst(x, app(x, _true)),
       cdr  = abst(x, app(x, _false));

  writeln("cons := ", cons.stringof);
  writeln("car  := ", car.stringof);
  writeln("cdr  := ", cdr.stringof);

  writeln("app(app(cons, one), two).normalize.stringof -> ", app(app(cons, one), two).normalize.stringof);
  writeln("app(app(cons, app(app(cons, one), two)), app(app(cons, one), two)).normalize.stringof -> ", app(app(cons, app(app(cons, one), two)), app(app(cons, one), two)).normalize.stringof);

  auto succ = abst(n, abst(f, abst(x, app(f, app(app(n, f), x)))));
  writeln("succ := ", succ.stringof);
  writeln("app(succ, zero).normalize.isEqualExpr(one) -> ", app(succ, zero).normalize.isEqualExpr(one));

  auto add = abst(a, abst(b, abst(f, abst(x, app(app(b, f), app(app(a, f), x))))));
  writeln("add := ", add.stringof);
  writeln("app(app(add, one), two).normalize.isEqualExpr(three) -> ", app(app(add, one), two).normalize.isEqualExpr(three));

  auto mul = abst(a, abst(b, abst(f, abst(x, app(app(b, app(a, f)), x)))));
  writeln("mul := ", mul.stringof);
  writeln("app(app(mul, two), three).normalize.isEqualExpr(genN(6)) -> ", app(app(mul, two), three).normalize.isEqualExpr(genN(6)));

  auto power = abst(a, abst(b, app(b, a)));
  writeln("power := ", power.stringof);
  writeln("app(app(power, three), two).normalize.isEqualExpr(genN(9)) -> ", app(app(power, three), two).normalize.isEqualExpr(genN(9)));

  auto pred = abst(n, abst(f, abst(x, app(cdr, app(app(n, abst(p, app(app(cons, app(f, app(car, p))), app(car, p)))),
                                                   app(app(cons, x), x))))));
  writeln("pred := ", pred.stringof);
  writeln("app(pred, three).normalize.isEqualExpr(two) -> ", app(pred, three).normalize.isEqualExpr(two));
  writeln("app(pred, zero).normalize.isEqualExpr(zero) -> ", app(pred, zero).normalize.isEqualExpr(zero));

  auto Y = abst(f, app(abst(x, app(f, app(x, x))), abst(x, app(f, app(x, x)))));
  writeln("Y := ", Y.stringof);

  auto Z = abst(f, app(abst(x, app(f, abst(y, app(app(x, x), y)))), abst(x, app(f, abst(y, app(app(x, x), y))))));
  writeln("Z := ", Z.stringof);

  auto fact_impl = abst(f, abst(n, app(app(app(_if, app(isZero, n)), one), app(app(mul, n), app(f, app(pred, n))))));
  auto fact = app(Y, fact_impl);
  writeln("fact_impl := ", fact_impl.stringof);
  writeln("fact := ", fact.stringof);
  writeln("app(fact, three).normalize.stringof -> ", app(fact, three).normalize.stringof);
}
