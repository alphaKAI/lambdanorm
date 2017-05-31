module lambdanorm.expr;
import std.algorithm,
       std.format,
       std.string,
       std.array,
       std.range,
       std.stdio;

interface Expr {
  string   stringof();
  string[] freeVars();
  void     replaceIdentifier(string, string);
  Expr     dup();
}

class Identifier : Expr {
  string identifier;

  this (string identifier) {
    this.identifier = identifier;
  }

  override string stringof() {
    return this.identifier;
  }

  string[] freeVars() {
    return [this.identifier].dup;
  }

  void replaceIdentifier(string pattern, string newIdentifier) {
    if (pattern == this.identifier) {
      this.identifier = newIdentifier;
    }
  }

  Identifier dup() {
    return new Identifier(this.identifier);
  }
}

class Abstraction : Expr {
  Identifier identifier;
  Expr       expr;

  this (Identifier identifier, Expr expr) {
    this.identifier = identifier;
    this.expr       = expr;
  }

  override string stringof() {
    return "(\\%s. %s)".format(this.identifier.stringof, this.expr.stringof);
  }

  string[] freeVars() {
    return expr.freeVars.filter!(x => x != this.identifier.stringof).array.dup;
  }

  void replaceIdentifier(string pattern, string newIdentifier) {
    this.identifier.replaceIdentifier(pattern, newIdentifier);
    this.expr.replaceIdentifier(pattern, newIdentifier);
  }

  Abstraction dup() {
    return new Abstraction(this.identifier.dup, this.expr.dup);
  }
}

bool isIdentifier(Expr expr) {
  if ((cast(Identifier)expr) !is null) {
    return true;
  } else {
    return false;
  }
}

class Application : Expr {
  Expr car,
       cdr;

  this (Expr car, Expr cdr) {
    this.car = car;
    this.cdr = cdr;
  }

  override string stringof() {
    string identifier = "%s",
           others     = "(%s)";

    string fmt = "%s %s".format(this.car.isIdentifier ? identifier : others,
                                this.cdr.isIdentifier ? identifier : others);

    return fmt.format(this.car.stringof, this.cdr.stringof);
  }

  string[] freeVars() {
    string[] vars_car = this.car.freeVars,
             vars_cdr = this.cdr.freeVars;

    return (vars_car ~ vars_cdr.filter!(x => ! vars_car.canFind(x)).array).dup;
  }

  void replaceIdentifier(string pattern, string newIdentifier) {
    this.car.replaceIdentifier(pattern, newIdentifier);
    this.cdr.replaceIdentifier(pattern, newIdentifier);
  }

  Application dup() {
    return new Application(this.car.dup, this.cdr.dup);
  }
}

Identifier ident(string identifier) {
  return new Identifier(identifier);
}

Abstraction abst(string identifier, Expr expr) {
  return new Abstraction(ident(identifier), expr);
}

Abstraction abst(Identifier identifier, Expr expr) {
  return new Abstraction(identifier, expr);
}

Application app(Expr car, Expr cdr) {
  return new Application(car, cdr);
}

Identifier freshVar(string identifier, string[] vars) {
  if (vars.canFind(identifier)) {
    return freshVar(identifier ~ "'", vars);
  } else {
    return ident(identifier);
  }
}

Identifier freshVar(Identifier identifier, string[] vars) {
  return freshVar(identifier.identifier, vars);
}

Expr substitute(Identifier var, Expr term, Expr expr) {
  if ((cast(Identifier)expr) !is null) {
    Identifier identifier = cast(Identifier)expr;
    string s = identifier.identifier;

    if (s == var.identifier) {
      return term;
    } else {
      return ident(s);
    }
  } else if ((cast(Abstraction)expr) !is null) {
    Abstraction abstraction = cast(Abstraction)expr;
    Identifier s = abstraction.identifier.dup;
    Expr       t = abstraction.expr.dup;

    auto t_vars    = t.freeVars,
         term_vars = term.freeVars;

    if (s.identifier == var.identifier) {
      return abst(s, t);
    } else if (! t_vars.canFind(var.identifier)) {
      return abst(s, t);
    } else if (term_vars.canFind(s.identifier)) {
      auto f = freshVar(s, t_vars ~ term_vars);

      t.replaceIdentifier(s.identifier, f.identifier);

      return abst(f, substitute(var, term, t));
    } else {
      return abst(s, substitute(var, term, t));
    }
  } else if ((cast(Application)expr) !is null) {
    Application appx = cast(Application)expr;
    Expr s = appx.car,
         t = appx.cdr;

    return app(substitute(var.dup, term.dup, s.dup), substitute(var.dup, term.dup, t.dup));
  }

  throw new Exception("Excep!");
}

bool is_redex(Expr expr) {
  if ((cast(Application)expr) !is null && {
        Application app = cast(Application)expr;
        return (cast(Abstraction)(app.car)) !is null;
    }()) {
      Application app = cast(Application)expr;
      Abstraction abs = cast(Abstraction)(app.car);
      Identifier  s   = abs.identifier;
      Expr        t   = abs.expr;
      Expr        u   = app.cdr;

      return true;
  } else {
    return false;
  }
}

Expr beta_reduce(Expr expr) {
  if ((cast(Application)expr) !is null && {
        Application app = cast(Application)expr;
        return (cast(Abstraction)(app.car)) !is null;
    }()) {
      Application app = cast(Application)expr;
      Abstraction abs = cast(Abstraction)(app.car);
      Identifier  s   = abs.identifier.dup;
      Expr        t   = abs.expr.dup;
      Expr        u   = app.cdr.dup;

      return substitute(s, u, t);
  } else {
    return expr;
  }
}

Expr normalize_step(Expr term) {
  if (term.is_redex) {
    return term.beta_reduce;//.nonrmalize;
  } else {
    if ((cast(Identifier)term) !is null) {
      return cast(Identifier)term;
    } else if ((cast(Abstraction)term) !is null) {
      Abstraction abstraction = cast(Abstraction)term;
      Identifier s = abstraction.identifier.dup;
      Expr       t = abstraction.expr.dup;

      return abst(s, normalize_step(t));
    } else if ((cast(Application)term) !is null) {
      Application appx = cast(Application)term;
      Expr t = appx.car.dup,
           u = appx.cdr.dup;

      auto normalizd_t = normalize_step(t);

      if (normalizd_t.isEqualExpr(t)) {
        return app(t, normalize_step(u));
      } else {
        return app(normalizd_t, u);//.normalize;
      }
    }
  }

  throw new Exception("Excep!");
}

Expr normalize(Expr term, bool showTerm = false) {
  if (showTerm) {
    writeln("normalize -> ", term.stringof);
  }

  auto normalizd_term = normalize_step(term);

  if (normalizd_term.isEqualExpr(term)) {
    return term;
  } else {
    //return normalize_step(normalizd_term);
    return normalizd_term.normalize;
  }
}

bool alpha_convertible(Expr term1, Expr term2) {
  if (((cast(Identifier)term2) !is null)) {
    string s2 = (cast(Identifier)term2).identifier;

    if ((cast(Identifier)term1) !is null) {
      string s1 = (cast(Identifier)term1).identifier;

      return s1 == s2;
    } else {
      return false;
    }
  } else if ((cast(Abstraction)term2) !is null) {
    Abstraction abs2 = cast(Abstraction)term2;
    auto s2 = abs2.identifier.dup,
         t2 = abs2.expr.dup;

    if ((cast(Abstraction)term1) !is null) {
      Abstraction abs1 = cast(Abstraction)term1;
      auto s1 = abs1.identifier.dup,
           t1 = abs1.expr.dup;

      if (s1 == s2) {
        return alpha_convertible(t1, t2);
      } else {
        return alpha_convertible(t1, substitute(s2, s1, t2));
      }
    } else {
      return false;
    }
  } else if ((cast(Application)term2) !is null) {
    Application app2 = cast(Application)term2;
    auto t2 = app2.car.dup,
         u2 = app2.cdr.dup;

    if ((cast(Application)term1) !is null) {
      Application app1 = cast(Application)term1;
      auto t1 = app1.car.dup,
           u1 = app1.cdr.dup;

      return alpha_convertible(t1, t2) && alpha_convertible(u1, u2);
    } else {
      return false;
    }
  }

  throw new Exception("Execp!");
}

bool isEqualExpr(Expr expr1, Expr expr2) {
  if (((cast(Identifier)expr1) !is null) && ((cast(Identifier)expr2) !is null)) {
    string id1 = (cast(Identifier)expr1).identifier,
           id2 = (cast(Identifier)expr2).identifier;

    return id1 == id2;
  } else if ((cast(Abstraction)expr1) !is null) {
    return alpha_convertible(expr1, expr2);
  } else if ((cast(Application)expr1) !is null) {
    return alpha_convertible(expr1, expr2);
  }

  return false;
}

bool isNumber(Expr expr) {
  if ((cast(Abstraction)expr) !is null && (cast(Abstraction)(cast(Abstraction)expr).expr) !is null) {

    for (auto z = ((cast(Abstraction)(cast(Abstraction)expr).expr).expr);
         (cast(Application)z) !is null; z = (cast(Application)z).cdr) {
      if ((cast(Application)z) is null) {
        return false;
      }
    }
    return true;
  } else {
    return false;
  }
}

size_t numberSize(Expr expr) {
  assert (isNumber(expr));

  size_t size;

  for (auto z = ((cast(Abstraction)(cast(Abstraction)expr).expr).expr);
      (cast(Application)z) !is null; z = (cast(Application)z).cdr) {
    size++;
  }

  return size;
}

Abstraction genN(size_t n) {
  auto f = ident("f"),
       x = ident("x"),
       y = ident("y");
  Expr ret = abst(f, abst(x, x));
  auto succ = abst(y, abst(f, abst(x, app(f, app(app(y, f), x)))));

  for (size_t i; i < n; i++) {
    ret = app(succ, ret).normalize;
  }

  return cast(Abstraction)ret;
}
