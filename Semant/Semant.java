package Semant;
import java.util.Hashtable;

import Translate.Exp;
import Types.Type;

public class Semant {
  Env env;

  public Semant(ErrorMsg.ErrorMsg err) {
    this(new Env(err));
  }

  Semant(Env e) {
    env = e;
  }

  public void transProg(Absyn.Exp exp) {
    transExp(exp);
  }

  private void error(int pos, String msg) {
    env.errorMsg.error(pos, msg);
  }

  static final Types.VOID   VOID   = new Types.VOID();
  static final Types.INT    INT    = new Types.INT();
  static final Types.STRING STRING = new Types.STRING();
  static final Types.NIL    NIL    = new Types.NIL();

  private Exp checkInt(ExpTy et, int pos) {
    if (!INT.coerceTo(et.ty))
      error(pos, "integer required");
    return et.exp;
  }

  private Exp checkComparable(ExpTy et, int pos)
  {
    Type a = et.ty.actual();
    if ((!(a instanceof INT)) && 
      (!(a instanceof STRING)) && 
      (!(a instanceof NIL)) && 
      (!(a instanceof RECORD)) && 
      (!(a instanceof ARRAY))) {
      error(pos, "integer, string, nil, record or array required");
    }
    return et.exp;
  }
  
  private Exp checkOrderable(ExpTy et, int pos)
  {
    Type a = et.ty.actual();
    if ((!(a instanceof INT)) && 
      (!(a instanceof STRING))) {
      error(pos, "integer or string required");
    }
    return et.exp;
  }

  ExpTy transExp(Absyn.Exp e) {
    ExpTy result;

    if (e == null)
      return new ExpTy(null, VOID);
    else if (e instanceof Absyn.OpExp)
      result = transExp((Absyn.OpExp)e);
    else if (e instanceof Absyn.LetExp)
      result = transExp((Absyn.LetExp)e);
    else if (e instanceof Absyn.VarExp)
      result = transExp((Absyn.VarExp)e);
    else if (e instanceof Absyn.NilExp)
      result = transExp((Absyn.NilExp)e);
    else if (e instanceof Absyn.IntExp)
      result = transExp((Absyn.IntExp)e);
    else if (e instanceof Absyn.StringExp)
      result = transExp((Absyn.StringExp)e);
    else if (e instanceof Absyn.CallExp)
      result = transExp((Absyn.CallExp)e);
    else if (e instanceof Absyn.RecordExp)
      result = transExp((Absyn.RecordExp)e);
    else if (e instanceof Absyn.SeqExp)
      result = transExp((Absyn.SeqExp)e);
    else if (e instanceof Absyn.AssignExp)
      result = transExp((Absyn.AssignExp)e);
    else if (e instanceof Absyn.IfExp)
      result = transExp((Absyn.IfExp)e);
    else if (e instanceof Absyn.WhileExp)
      result = transExp((Absyn.WhileExp)e);
    else if (e instanceof Absyn.ForExp)
      result = transExp((Absyn.ForExp)e);
    else if (e instanceof Absyn.BreakExp)
      result = transExp((Absyn.BreakExp)e);
    else if (e instanceof Absyn.ArrayExp)
      result = transExp((Absyn.ArrayExp)e);
    else throw new Error("Semant.transExp");
    e.type = result.ty;
    return result;
  }


  ExpTy transExp(OpExp e) {
    ExpTy left = transExp(e.left);
    ExpTy right = transExp(e.right);

    switch (e.oper) {
    case Absyn.OpExp.PLUS:
      checkInt(left, e.left.pos);
      checkInt(right, e.right.pos);
      return new ExpTy(null, INT);
    default:
      throw new Error("unknown operator");
    }
  }

  ExpTy transExp(LetExp e) {
    env.venv.beginScope();
    env.tenv.beginScope();
    for (Absyn.DecList d = e.decs; d != null; d = d.tail) {
      transDec(d.head);
    }
    ExpTy body = transExp(e.body);
    env.venv.endScope();
    env.tenv.endScope();
    return new ExpTy(null, body.ty);
  }

  ExpTy transExp(VarExp e)
  {
    return new ExpTy(null, NIL);
  }

  ExpTy transExp(NilExp e)
  {
    return new ExpTy(null, NIL);
  }
  
  ExpTy transExp(IntExp e)
  {
    return new ExpTy(null, INT);
  }
  
  ExpTy transExp(StringExp e)
  {
    return new ExpTy(null, STRING);
  }
  
  ExpTy transExp(CallExp e)
  {
    Entry x = (Entry)this.env.venv.get(e.func);
    if ((x instanceof FunEntry))
    {
      FunEntry f = (FunEntry)x;
      transArgs(e.pos, f.formals, e.args);
      return new ExpTy(null, f.result);
    }
    error(e.pos, "undeclared function: " + e.func);
    return new ExpTy(null, VOID);
  }
  
  private void transArgs(int epos, RECORD formal, ExpList args)
  {
    if (formal == null)
    {
      if (args != null) {
        error(args.head.pos, "too many arguments");
      }
      return;
    }
    if (args == null)
    {
      error(epos, "missing argument for " + formal.fieldName);
      return;
    }
    ExpTy e = transExp(args.head);
    if (!e.ty.coerceTo(formal.fieldType)) {
      error(args.head.pos, "argument type mismatch");
    }
    transArgs(epos, formal.tail, args.tail);
  }

  ExpTy transExp(RecordExp e)
  {
    return new ExpTy(null, STRING);
  }

  ExpTy transExp(SeqExp e)
  {
    return new ExpTy(null, STRING);
  }

  ExpTy transExp(AssignExp e)
  {
    return new ExpTy(null, STRING);
  }

  ExpTy transExp(IfExp e)
  {
    return new ExpTy(null, STRING);
  }

  ExpTy transExp(WhileExp e)
  {
    return new ExpTy(null, STRING);
  }

  ExpTy transExp(ForExp e)
  {
    return new ExpTy(null, STRING);
  }

  ExpTy transExp(BreakExp e)
  {
    return new ExpTy(null, STRING);
  }

  ExpTy transExp(ArrayExp e)
  {
    return new ExpTy(null, STRING);
  }

  ExpTy transVar(Var v)
  {
    return transVar(v, false);
  }
  
  ExpTy transVar(Var v, boolean lhs)
  {
    if ((v instanceof SimpleVar)) {
      return transVar((SimpleVar)v, lhs);
    }
    if ((v instanceof FieldVar)) {
      return transVar((FieldVar)v);
    }
    if ((v instanceof SubscriptVar)) {
      return transVar((SubscriptVar)v);
    }
    throw new Error("Semant.transVar");
  }
  
  private void transFields(int epos, RECORD f, FieldExpList exp)
  {
    if (f == null)
    {
      if (exp != null) {
        error(exp.pos, "too many expressions");
      }
      return;
    }
    if (exp == null)
    {
      error(epos, "missing expression for " + f.fieldName);
      return;
    }
    ExpTy e = transExp(exp.init);
    if (exp.name != f.fieldName) {
      error(exp.pos, "field name mismatch");
    }
    if (!e.ty.coerceTo(f.fieldType)) {
      error(exp.pos, "field type mismatch");
    }
    transFields(epos, f.tail, exp.tail);
  }
  
  ExpTy transVar(SimpleVar v, boolean lhs)
  {
    Entry x = (Entry)this.env.venv.get(v.name);
    if ((x instanceof VarEntry))
    {
      VarEntry ent = (VarEntry)x;
      if ((lhs) && ((ent instanceof LoopVarEntry))) {
        error(v.pos, "assignment to loop index");
      }
      return new ExpTy(null, ent.ty);
    }
    error(v.pos, "undeclared variable: " + v.name);
    return new ExpTy(null, VOID);
  }
  
  ExpTy transVar(FieldVar v)
  {
    ExpTy var = transVar(v.var);
    Type actual = var.ty.actual();
    if ((actual instanceof RECORD))
    {
      for (RECORD field = (RECORD)actual; field != null; field = field.tail) {
        if (field.fieldName == v.field) {
          return new ExpTy(null, field.fieldType);
        }
      }
      error(v.pos, "undeclared field: " + v.field);
    }
    else
    {
      error(v.var.pos, "record required");
    }
    return new ExpTy(null, VOID);
  }
  
  ExpTy transVar(SubscriptVar v)
  {
    ExpTy var = transVar(v.var);
    ExpTy index = transExp(v.index);
    checkInt(index, v.index.pos);
    Type actual = var.ty.actual();
    if ((actual instanceof ARRAY))
    {
      ARRAY array = (ARRAY)actual;
      return new ExpTy(null, array.element);
    }
    error(v.var.pos, "array required");
    return new ExpTy(null, VOID);
  }

  Exp transDec(Absyn.Dec d) {
    if (d instanceof Absyn.VarDec)
      return transDec((Absyn.VarDec)d);
    throw new Error("Semant.transDec");
  }

  Exp transDec(Absyn.VarDec d) {
    // NOTE: THIS IMPLEMENTATION IS INCOMPLETE
    // It is here to show you the general form of the transDec methods
    ExpTy init = transExp(d.init);
    Type type;
    if (d.typ == null) {
      type = init.ty;
    } else {
      type = VOID;
      throw new Error("unimplemented");
    }
    d.entry = new VarEntry(type);
    env.venv.put(d.name, d.entry);
    return null;
  }
  Exp transDec(Absyn.TypeDec d)
  {
    Hashtable hash = new Hashtable();
    for (TypeDec type = d; type != null; type = type.next)
    {
      if (hash.put(type.name, type.name) != null) {
        error(type.pos, "type redeclared");
      }
      type.entry = new NAME(type.name);
      this.env.tenv.put(type.name, type.entry);
    }
    for (TypeDec type = d; type != null; type = type.next)
    {
      NAME name = type.entry;
      name.bind(transTy(type.ty));
    }
    for (TypeDec type = d; type != null; type = type.next)
    {
      NAME name = type.entry;
      if (name.isLoop()) {
        error(type.pos, "illegal type cycle");
      }
    }
    return null;
  }

  Exp transTy(Absyn.TypeDec d) {
    //implement
  }

  Exp transTy(Absyn.FunctionDec d) {
    //implement
  }

  Exp transTy(Absyn.TypeDec d) {
    //implement
  }

  Exp transTy(Absyn.TypeDec d) {
    //implement
  }

  Exp putTypeFields(Absyn.Vardec d){
    //implement
  }

  Exp transTypeFields(Hashtable h, Absyn.FunctionDec d) {
    //implement
  }
  
  Exp transDec(Absyn.FunctionDec d)
  {
    Hashtable hash = new Hashtable();
    for (FunctionDec f = d; f != null; f = f.next)
    {
      if (hash.put(f.name, f.name) != null) {
        error(f.pos, "function redeclared");
      }
      RECORD fields = transTypeFields(new Hashtable(), f.params);
      Type type = transTy(f.result);
      f.entry = new FunEntry(fields, type);
      this.env.venv.put(f.name, f.entry);
    }
    for (FunctionDec f = d; f != null; f = f.next)
    {
      this.env.venv.beginScope();
      putTypeFields(f.entry.formals);
      Semant fun = new Semant(this.env);
      ExpTy body = fun.transExp(f.body);
      if (!body.ty.coerceTo(f.entry.result)) {
        error(f.body.pos, "result type mismatch");
      }
      this.env.venv.endScope();
    }
    return null;
  }
}

