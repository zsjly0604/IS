structure MipsFrame : FRAME =
struct
  
  datatype access =  InFrame of int
                   | InReg of Temp.temp
  type frame = {name: Temp.label, formals: access list, locals: int ref, offset:int ref}
  val wordSize = 4
  val RV = Temp.newtemp()
  val FP = Temp.newtemp()
  datatype frag = PROC of {body:Tree.stm, frame:frame}
		| STRING of Temp.label * string

  datatype register = Reg of string

  val ZERO = Temp.newtemp()		  
  val AT = Temp.newtemp()
  val RV = Temp.newtemp()
  val RV' = Temp.newtemp()

  val a0 = Temp.newtemp()
  val a1 = Temp.newtemp()
  val a2 = Temp.newtemp()
  val a3 = Temp.newtemp()

  val t0 = Temp.newtemp()
  val t1 = Temp.newtemp()
  val t2 = Temp.newtemp()
  val t3 = Temp.newtemp()
  val t4 = Temp.newtemp()
  val t5 = Temp.newtemp()
  val t6 = Temp.newtemp()
  val t7 = Temp.newtemp()
  val t8 = Temp.newtemp()
  val t9 = Temp.newtemp()

  val s0 = Temp.newtemp()
  val s1 = Temp.newtemp()
  val s2 = Temp.newtemp()
  val s3 = Temp.newtemp()
  val s4 = Temp.newtemp()
  val s5 = Temp.newtemp()
  val s6 = Temp.newtemp()
  val s7 = Temp.newtemp()
  val s8 = Temp.newtemp()

  val GP = Temp.newtemp()
  val SP = Temp.newtemp()
  val RA = Temp.newtemp()
  
  val specialregs = [(ZERO, Reg "ZERO"),(AT, Reg "AT"),(RV, Reg "RV"),(RV', Reg "RV'"),(GP, Reg "GP"), (SP, Reg "SP"),(RA, Reg "RA")]

  val argregs = [(a0, Reg "a0"),(a1, Reg "a1"),(a2, Reg "a2"),(a3, Reg "a3") ]

  val calleesaves = [(s0, Reg "s0"),(s1, Reg "s1"),(s2, Reg "s2"),(s3, Reg "s3"),(s4, Reg "s4"),(s5, Reg "s5"),(s6, Reg "s6"),(s7, Reg "s7")]

  val callersaves = [(t0, Reg "t0"), (t1, Reg"t1"),(t2, Reg "t2"), (t3, Reg"t3"),(t4, Reg "t4"), (t5, Reg"t5"),(t6, Reg "t6"), (t7, Reg"t7"),(t8, Reg "t8"), (t9, Reg"t9")]

  val tempMap = foldl (fn ((temp,reg), table) => Temp.enter(table,temp,reg)) Temp.empty specialregs

  
  fun lookreg temp =
      case Temp.Table.look(tempMap,temp) of
	  NONE => Temp.makestring(temp)
	| SOME(Reg register) => register
				    
		  
  fun name (f:frame) = #name f
  
  fun formals (f:frame) = #formals f
  
  fun allocLocal ({name = name, formals = formals, offset = offset, locals = locals}) =
      let val CurrOffset = offset		  
      fun allocLoc(escape) = if escape
			     then (CurrOffset := !CurrOffset - wordSize;(locals := !locals+1);InFrame(!CurrOffset))
			     else InReg(Temp.newtemp())
      in
	  allocLoc
      end
      
  fun newFrame ({name:Temp.label, formals = formals}) =
      let val tempoffset = ref 0
	  fun allocFrame(escape) = if escape
				   then (tempoffset := !tempoffset -wordSize; InFrame(!tempoffset))
				   else InReg(Temp.newtemp())
      in
	  {name = name, formals = (map allocFrame formals),offset = tempoffset, locals = ref 0 }
      end

				  
  fun exp (InFrame(k)) = 
      let
	  fun getexp(framePointer) =
	      Tree.MEM(Tree.BINOP(Tree.PLUS, framePointer, Tree.CONST(k)))
      in
       getexp
      end
    | exp (InReg(temp)) = 
      let
	  fun getexp(_) = Tree.TEMP(temp)
      in
          getexp
      end 

    fun externalCall (funcname, args) =
       Tree.CALL(Tree.NAME(Temp.namedlabel funcname), args)

    fun procEntryExit1 (frame,body)=body

    fun gettemp (temp,register) = temp

    fun procEntryExit2 (frame,body)=
	body @ [Assem.OPER{assem = "", src = (map gettemp specialregs)@(map gettemp calleesaves), dst=[], jump=SOME[]}]

    fun procEntryExit3 ({name=name, formals=formals, locals=locals},  body : Assem.instr list) =
	{prolog = "PROCEDURE " ^ Symbol.name name ^ "\n",
	 body = body,
	 epilog = "END " ^ Symbol.name name ^ "\n"}

	
end
