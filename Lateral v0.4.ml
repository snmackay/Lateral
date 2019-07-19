(* Lateral V0.4 Beta
 * Sean Mackay
 * snmackay@buffalo.edu
 * 3/30/19                          *)

exception Foo of string
type const = BOOL of bool| INT of int | FLO of float | ERROR | S of string | N of string | UNIT | FUNCT of const*const*(command list)*(const*const) list list
and
command = PUSH of const | PUSHI of int | PUSHF of float | PUSHS of string | PUSHN of string | PUSHB of bool | POP | ADD | SUB | MUL | DIV | REM | ROW | NEG | SWAP | QUIT | CAT | AND | OR | NOT | EQUAL | LESS | BIND | IF | LET | END | FUN of string*string | RETURN | FUNEND |  CALL | INOUTFUN of string*string



let interpreter (inFile,outFile) :unit=

let ic = open_in inFile in

let oc = open_out outFile in

let rec loop_read acc =

    try

        let l = input_line ic in loop_read (l::acc)
    with

    | End_of_file -> acc in

let rec acc =loop_read [] in

let rec writeOut ((constList: const list list),bindList) : unit  =
    match constList with
      |[]::back -> writeOut(back,bindList)
      |front::back -> (
                 match front with
                 |hd::tl -> (
                          match hd with
                          |INT(a) -> (
                              Printf.fprintf oc "%s\n" (string_of_int a);
                              writeOut (((tl)::back),bindList))
                          |FLO(a) -> (
                              Printf.fprintf oc "%s\n" (string_of_float a);
                              writeOut (((tl)::back),bindList))
                          |BOOL(a) -> (
                              Printf.fprintf oc "%s\n" (":"^(string_of_bool a)^":");
                              writeOut (((tl)::back),bindList))
                          |S(a) -> (
                              Printf.fprintf oc "%s\n" (String.sub a 1 ((String.length a)-2));
                              writeOut (((tl)::back),bindList ))
                          |N(a) -> (
                              Printf.fprintf oc "%s\n" a;
                              writeOut (((tl)::back) ,bindList))
                          |ERROR -> (
                              Printf.fprintf oc "%s\n" ":error:";
                              writeOut (((tl)::back),bindList))
                          |UNIT -> (
                              Printf.fprintf oc "%s\n" ":unit:";
                              writeOut (((tl)::back ),bindList))
                          | _ -> writeOut (((tl)::back),bindList)

                          )
                 |[] -> writeOut (back,bindList)
                 )
     |_ ->close_out oc


in


let rec bindListHas (bindList,name) :const =
    match bindList with
    |[] -> ERROR
    |hd::tl -> (
               match hd with
               |(N(a),INT(rl))::tr-> (
                                         match (compare name a ) with
                                         | 0 -> INT(rl)
                                         | _ -> bindListHas(tr::tl,name)
                                        )
               |(N(a),BOOL(rl))::tr -> (
                                         match (compare name a ) with
                                         | 0 -> BOOL(rl)
                                         | _ -> bindListHas(tr::tl,name)
                                        )
               |(N(a),FLO(rl))::tr -> (
                                         match (compare name a ) with
                                         | 0 -> FLO(rl)
                                         | _ -> bindListHas(tr::tl,name)
                                      )
               |(N(a),S(rl))::tr -> (
                                         match (compare name a ) with
                                         | 0 -> S(rl)
                                         | _ -> bindListHas(tr::tl,name)
                                        )
               |(N(a),UNIT)::tr -> (
                                         match (compare name a ) with
                                         | 0 -> UNIT
                                         | _ -> bindListHas(tr::tl,name)
                                        )
               |(N(a),N(rl))::tr -> (bindListHas(bindList,rl))
               |(N(a),FUNCT(b,c,d,e))::tr -> (
                                            match(compare name a) with
                                            | 0 -> FUNCT(b,c,d,e)
                                            |_ -> bindListHas(tr::tl,name)
                                           )
               | _ -> bindListHas(tl,name)
               )
in
(*print_endline(string_of_int(List.length funCommands)*)
(*(N(name),FUNCT(N(param),c,bindList))::*)
let rec makeClosure (scopeCounter,funCommands,remCommands) =
  match scopeCounter,remCommands with
  |a,FUN(name1,param1)::tl -> makeClosure(a+1,FUN(name1,param1)::funCommands,tl)
  |0,FUNEND::tl -> (List.rev(FUNEND::funCommands),tl)
  |_,FUNEND::tl -> makeClosure(scopeCounter-1,FUNEND::funCommands,tl)
  |_,a::tl -> makeClosure(scopeCounter,a::funCommands,tl)
in

let rec addToTuple (commandList,(constList :const list list),(bindList :(const*const) list list)  ) :(const list list)*(const*const)list list =
  match commandList,constList,bindList with
      |FUN(name,param)::rl,hd::tl,a::b->(
                                         match makeClosure(0,[],rl) with
                                         |c,d -> addToTuple(d,(UNIT::hd)::tl,((N(name),FUNCT(N(param),INT(0),c,bindList))::a)::b)
                                        )
      |INOUTFUN(name,param)::rl,hd::tl,a::b-> (
                                               match makeClosure(0,[],rl) with
                                               |c,d -> addToTuple(d,(UNIT::hd)::tl,((N(name),FUNCT(N(param),INT(1),c,bindList))::a)::b)
                                              )
      |RETURN::FUNEND::rl,_,_ -> constList,bindList
      |CALL::rl,(ERROR::N(funName)::a)::tl,_ -> addToTuple(rl,(ERROR::ERROR::N(funName)::a)::tl,bindList)
      |CALL::rl,(ERROR::FUNCT(c,d,e,f)::a)::tl,_ -> addToTuple(rl,(ERROR::ERROR::FUNCT(c,d,e,f)::a)::tl,bindList)
      |CALL::rl,(N(param)::FUNCT(N(c),d,e,f)::a)::tl,_ -> (match bindListHas(bindList,param)with
                                                      |ERROR -> addToTuple(rl,(ERROR::a)::tl,bindList)
                                                      |v -> (let result=addToTuple(BIND::e,(v::N(c)::[])::[],f)in
                                                             match result,FUNCT(N(c),d,e,f) with
                                                             |((k::l)::m,k2),FUNCT(N(c),INT(1),e,f) -> (print_endline "beep";match bindListHas(k2,c) with
                                                                                                        |ERROR -> addToTuple(rl,(ERROR::a)::tl,bindList)
                                                                                                        |enclosval -> addToTuple(BIND::POP::rl,(enclosval::N(param)::a)::tl,bindList)
                                                                                                       )
                                                             |((N(k)::l)::m,k2),FUNCT(c,INT(0),e,f) -> (match bindListHas(k2,k) with
                                                                                                        |ERROR -> addToTuple(rl,(N(k)::a)::tl,bindList)
                                                                                                        |enclosval -> addToTuple(rl,(enclosval::a)::tl,bindList)
                                                                                                       )
                                                             |((k::l)::m,k2),FUNCT(c,INT(0),e,f) -> addToTuple(rl,(k::a)::tl,bindList)
                                                            )

                                                      )

      |CALL::rl,(param::FUNCT(c,d,e,f)::a)::tl,_ -> (let result=addToTuple(BIND::e,(param::c::[])::[],f)in
                                                   match result with
                                                   |(N(k)::l)::m,k2 -> (match bindListHas(k2,k) with
                                                                        |ERROR -> addToTuple(rl,(N(k)::a)::tl,bindList)
                                                                        |enclosval -> addToTuple(rl,(enclosval::a)::tl,bindList)
                                                                       )
                                                   |(k::l)::m,k2 -> addToTuple(rl,(k::a)::tl,bindList)
                                                   |_ -> addToTuple(rl,(ERROR::a)::tl,bindList)
                                                  )
      |CALL::rl,(N(param)::N(funName)::a)::tl,_ -> (
                                                match bindListHas(bindList,funName)with
                                                |FUNCT(N(c),d,e,f) -> (match bindListHas(bindList,param)with
                                                                    |ERROR -> addToTuple(rl,(ERROR::a)::tl,bindList)
                                                                    |v -> (let result=addToTuple(BIND::e,(v::N(c)::[])::[],f@((N(funName),FUNCT(N(c),d,e,f))::[])::[])in

                                                                           match result,FUNCT(N(c),d,e,f) with
                                                                           |((k::l)::m,k2),FUNCT(N(c),INT(1),e,f) -> (print_endline "beep";match bindListHas(k2,c) with
                                                                                                                    |ERROR -> addToTuple(rl,(ERROR::a)::tl,bindList)
                                                                                                                    |enclosval -> addToTuple(BIND::POP::rl,(enclosval::N(param)::a)::tl,bindList)
                                                                                                                  )
                                                                           |((N(k)::l)::m,k2),FUNCT(c,INT(0),e,f) -> (match bindListHas(k2,k) with
                                                                                                                      |ERROR -> addToTuple(rl,(N(k)::a)::tl,bindList)
                                                                                                                      |enclosval -> addToTuple(rl,(enclosval::a)::tl,bindList)
                                                                                                                     )
                                                                           |((k::l)::m,k2),FUNCT(c,INT(0),e,f) -> addToTuple(rl,(k::a)::tl,bindList)

                                                                          )


                                                                 )
                                                |_-> addToTuple(rl,(ERROR::N(param)::N(funName)::a)::tl,bindList)
                                                  )
      |CALL::rl,(param::N(funName)::a)::tl,_ -> (match bindListHas(bindList,funName) with
                                                 |FUNCT(c,d,e,f) -> (let result=addToTuple(BIND::e,(param::c::[])::[],f@((N(funName),FUNCT(c,d,e,f))::[])::[])in
                                                                   match result with
                                                                   |(N(k)::l)::m,k2 -> (match bindListHas(k2,k) with
                                                                                        |ERROR -> addToTuple(rl,(N(k)::a)::tl,bindList)
                                                                                        |enclosval -> addToTuple(rl,(enclosval::a)::tl,bindList)
                                                                                       )
                                                                   |(k::l)::m,k2 -> addToTuple(rl,(k::a)::tl,bindList)
                                                                   |_ -> addToTuple(rl,(ERROR::a)::tl,bindList)
                                                                  )
                                                 |_-> addToTuple(rl,(ERROR::param::N(funName)::a)::tl,bindList)
                                                )
      |(PUSHB(a)::rl,hd::tl,_) -> addToTuple (rl,(BOOL(a)::hd)::tl,bindList)
      |(PUSHI(a)::rl,(aa)::tl,_) -> addToTuple (rl,(INT(a)::aa)::tl,bindList)
      |(PUSHF(a)::rl,(aa)::tl,_) -> addToTuple (rl,(FLO(a)::aa)::tl,bindList)
      |(PUSHS(a)::rl,(aa)::tl,_) -> addToTuple (rl,(S(a)::aa)::tl,bindList)
      |(PUSHN(a)::rl,(aa)::tl,_) -> addToTuple (rl,(N(a)::aa)::tl,bindList)
      |(PUSH(a)::rl,(aa)::tl,_) -> addToTuple (rl,(a::aa)::tl,bindList)
      |(POP::rl,[]::tl,_)-> addToTuple (rl,(ERROR::[])::tl,bindList)
      |(POP::rl,(hi::ti)::tl,_)-> addToTuple (rl,(ti)::tl,bindList)

(*///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////*)
      (*Addition commands*)
      |(ADD::rl,(INT(a)::INT(b)::ti)::tl,_) -> addToTuple (rl,(INT(a+b)::ti)::tl,bindList)
      |(ADD::rl,(N(a)::INT(b)::ti)::tl,_) -> (
                                             match bindListHas(bindList, a) with
                                             | INT(k) -> addToTuple (rl,(INT(k+b)::ti)::tl,bindList)
                                             | FLO(k) -> addToTuple (rl,(FLO(((float_of_int(b))+.k))::ti)::tl,bindList)
                                             | _ -> addToTuple (rl,(ERROR::N(a)::INT(b)::ti)::tl,bindList)
                                             )
      |(ADD::rl,(INT(a)::N(b)::ti)::tl,_) -> (
                                             match bindListHas(bindList, b) with
                                             | INT(k) -> addToTuple (rl,(INT(k+a)::ti)::tl,bindList)
                                             | FLO(k) -> addToTuple (rl,(FLO(((float_of_int(a))+.k))::ti)::tl,bindList)
                                             | _ -> addToTuple (rl,(ERROR::INT(a)::N(b)::ti)::tl,bindList)
                                             )
      |(ADD::rl,(N(a)::N(b)::ti)::tl,_) -> (
                                           match (bindListHas(bindList, a),bindListHas(bindList, b)) with
                                           | (INT(k),INT(l)) -> addToTuple (rl,(INT(k+l)::ti)::tl,bindList)
                                           | (FLO(k),INT(l)) -> addToTuple (rl,(FLO((float_of_int(l)) +. k)::ti)::tl,bindList)
                                           | (FLO(k),FLO(l)) -> addToTuple (rl,(FLO(k +. l)::ti)::tl,bindList)
                                           | (INT(k),FLO(l)) -> addToTuple (rl,(FLO((float_of_int(k)) +. l)::ti)::tl,bindList)
                                           | _,_ -> addToTuple (rl,(ERROR::N(a)::N(b)::ti)::tl,bindList)
                                           )
      |(ADD::rl,(FLO(a)::FLO(b)::ti)::tl,_) -> addToTuple (rl,(FLO(a +. b)::ti)::tl,bindList)
      |(ADD::rl,(N(a)::FLO(b)::ti)::tl,_) -> (
                                             match bindListHas(bindList, a) with
                                             | INT(k) -> addToTuple (rl,(FLO((float_of_int(k)) +. b)::ti)::tl,bindList)
                                             | FLO(k) -> addToTuple (rl,(FLO(k +. b)::ti)::tl,bindList)
                                             | _ -> addToTuple (rl,(ERROR::N(a)::FLO(b)::ti)::tl,bindList)
                                             )
      |(ADD::rl,(FLO(a)::N(b)::ti)::tl,_) -> (
                                             match bindListHas(bindList, b) with
                                             | INT(k) -> addToTuple (rl,(FLO(float_of_int(k) +. a)::ti)::tl,bindList)
                                             | FLO(k) -> addToTuple (rl,(FLO(k +. a)::ti)::tl,bindList)
                                             | _ -> addToTuple (rl,(ERROR::FLO(a)::N(b)::ti)::tl,bindList)
                                             )
      |(ADD::rl,(FLO(a)::INT(b)::ti)::tl,_) -> addToTuple (rl,(FLO((float_of_int(b)) +. a)::ti)::tl,bindList)
      |(ADD::rl,(INT(a)::FLO(b)::ti)::tl,_) -> addToTuple (rl,(FLO((float_of_int(a)) +. b)::ti)::tl,bindList)

(*///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////*)
      (*Subtraction commands*)
      |(SUB::rl,(INT(a)::INT(b)::ti)::tl,_) -> addToTuple (rl,(INT(a-b)::ti)::tl,bindList)
      |(SUB::rl,(N(a)::INT(b)::ti)::tl,_) -> (
                                             match bindListHas(bindList, a) with
                                             | INT(k) -> addToTuple (rl,(INT(k-b)::ti)::tl,bindList)
                                             | FLO(k) -> addToTuple (rl,(FLO(((float_of_int(b))-.k))::ti)::tl,bindList)
                                             | _ -> addToTuple (rl,(ERROR::N(a)::INT(b)::ti)::tl,bindList)
                                             )
      |(SUB::rl,(INT(a)::N(b)::ti)::tl,_) -> (
                                             match bindListHas(bindList, b) with
                                             | INT(k) -> addToTuple (rl,(INT(k-a)::ti)::tl,bindList)
                                             | FLO(k) -> addToTuple (rl,(FLO((k-.(float_of_int(a))))::ti)::tl,bindList)
                                             | _ -> addToTuple (rl,(ERROR::INT(a)::N(b)::ti)::tl,bindList)
                                             )
      |(SUB::rl,(N(a)::N(b)::ti)::tl,_) -> (
                                           match (bindListHas(bindList, a),bindListHas(bindList, b)) with
                                           | (INT(k),INT(l)) -> addToTuple (rl,(INT(l-k)::ti)::tl,bindList)
                                           | (FLO(k),INT(l)) -> addToTuple (rl,(FLO((float_of_int(l)) -. k)::ti)::tl,bindList)
                                           | (FLO(k),FLO(l)) -> addToTuple (rl,(FLO(l -. k)::ti)::tl,bindList)
                                           | (INT(k),FLO(l)) -> addToTuple (rl,(FLO((l-. float_of_int(k)))::ti)::tl,bindList)
                                           | _,_ -> addToTuple (rl,(ERROR::N(a)::N(b)::ti)::tl,bindList)
                                           )
      |(SUB::rl,(FLO(a)::FLO(b)::ti)::tl,_) -> addToTuple (rl,(FLO(b -. a)::ti)::tl,bindList)
      |(SUB::rl,(N(a)::FLO(b)::ti)::tl,_) -> (
                                             match bindListHas(bindList, a) with
                                             | INT(k) -> addToTuple (rl,(FLO((b -. float_of_int(k)))::ti)::tl,bindList)
                                             | FLO(k) -> addToTuple (rl,(FLO(b -. k)::ti)::tl,bindList)
                                             | _ -> addToTuple (rl,(ERROR::N(a)::FLO(b)::ti)::tl,bindList)
                                             )
      |(SUB::rl,(FLO(a)::N(b)::ti)::tl,_) -> (
                                             match bindListHas(bindList, b) with
                                             | INT(k) -> addToTuple (rl,(FLO(float_of_int(k) -. a)::ti)::tl,bindList)
                                             | FLO(k) -> addToTuple (rl,(FLO(k -. a)::ti)::tl,bindList)
                                             | _ -> addToTuple (rl,(ERROR::FLO(a)::N(b)::ti)::tl,bindList)
                                             )
      |(SUB::rl,(FLO(a)::INT(b)::ti)::tl,_) -> addToTuple (rl,(FLO((float_of_int(b)) -. a)::ti)::tl,bindList)
      |(SUB::rl,(INT(a)::FLO(b)::ti)::tl,_) -> addToTuple (rl,(FLO(b -. (float_of_int(a)))::ti)::tl,bindList)

(*///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////*)
      (*Multiplication commands*)
      |(MUL::rl,(INT(a)::INT(b)::ti)::tl,_) -> addToTuple (rl,(INT(a*b)::ti)::tl,bindList)
      |(MUL::rl,(N(a)::INT(b)::ti)::tl,_) -> (
                                             match bindListHas(bindList, a) with
                                             | INT(k) -> addToTuple (rl,(INT(k*b)::ti)::tl,bindList)
                                             | FLO(k) -> addToTuple (rl,(FLO(((float_of_int(b))*.k))::ti)::tl,bindList)
                                             | _ -> addToTuple (rl,(ERROR::N(a)::INT(b)::ti)::tl,bindList)
                                             )
      |(MUL::rl,(INT(a)::N(b)::ti)::tl,_) -> (
                                             match bindListHas(bindList, b) with
                                             | INT(k) -> addToTuple (rl,(INT(k*a)::ti)::tl,bindList)
                                             | FLO(k) -> addToTuple (rl,(FLO(((float_of_int(a))*.k))::ti)::tl,bindList)
                                             | _ -> addToTuple (rl,(ERROR::INT(a)::N(b)::ti)::tl,bindList)
                                             )
      |(MUL::rl,(N(a)::N(b)::ti)::tl,_) -> (
                                           match (bindListHas(bindList, a),bindListHas(bindList, b)) with
                                           | (INT(k),INT(l)) -> addToTuple (rl,(INT(l*k)::ti)::tl,bindList)
                                           | (FLO(k),INT(l)) -> addToTuple (rl,(FLO((float_of_int(l)) *. k)::ti)::tl,bindList)
                                           | (FLO(k),FLO(l)) -> addToTuple (rl,(FLO(l *. k)::ti)::tl,bindList)
                                           | (INT(k),FLO(l)) -> addToTuple (rl,(FLO((l *. float_of_int(k)))::ti)::tl,bindList)
                                           | _,_ -> addToTuple (rl,(ERROR::N(a)::N(b)::ti)::tl,bindList)
                                           )
      |(MUL::rl,(FLO(a)::FLO(b)::ti)::tl,_) -> addToTuple (rl,(FLO(b *. a)::ti)::tl,bindList)
      |(MUL::rl,(N(a)::FLO(b)::ti)::tl,_) -> (
                                             match bindListHas(bindList, a) with
                                             | INT(k) -> addToTuple (rl,(FLO((b *. float_of_int(k)))::ti)::tl,bindList)
                                             | FLO(k) -> addToTuple (rl,(FLO(b *. k)::ti)::tl,bindList)
                                             | _ -> addToTuple (rl,(ERROR::N(a)::FLO(b)::ti)::tl,bindList)
                                             )
      |(MUL::rl,(FLO(a)::N(b)::ti)::tl,_) -> (
                                             match bindListHas(bindList, b) with
                                             | INT(k) -> addToTuple (rl,(FLO(float_of_int(k) *. a)::ti)::tl,bindList)
                                             | FLO(k) -> addToTuple (rl,(FLO(k *. a)::ti)::tl,bindList)
                                             | _ -> addToTuple (rl,(ERROR::FLO(a)::N(b)::ti)::tl,bindList)
                                             )
      |(MUL::rl,(FLO(a)::INT(b)::ti)::tl,_) -> addToTuple (rl,(FLO((float_of_int(b)) *. a)::ti)::tl,bindList)
      |(MUL::rl,(INT(a)::FLO(b)::ti)::tl,_) -> addToTuple (rl,(FLO(b *. (float_of_int(a)))::ti)::tl,bindList)

(*///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////*)
      (*Division commands*)
      |(DIV::rl,(INT(0)::ti)::tl,_) -> addToTuple (rl,(ERROR::INT(0)::ti)::constList,bindList)
      |(DIV::rl,(FLO(0.0)::ti)::tl,_) -> addToTuple (rl,(ERROR::FLO(0.0)::ti)::constList,bindList)

      |(DIV::rl,(INT(a)::INT(b)::ti)::tl,_) -> addToTuple (rl,(INT(a/b)::ti)::tl,bindList)
      |(DIV::rl,(N(a)::INT(b)::ti)::tl,_) -> (
                                             match bindListHas(bindList, a) with
                                             | INT(k) -> addToTuple (rl,(INT(k/b)::ti)::tl,bindList)
                                             | FLO(k) -> addToTuple (rl,(FLO(((float_of_int(b))/.k))::ti)::tl,bindList)
                                             | _ -> addToTuple (rl,(ERROR::N(a)::INT(b)::ti)::tl,bindList)
                                             )
      |(DIV::rl,(INT(a)::N(b)::ti)::tl,_) -> (
                                             match bindListHas(bindList, b) with
                                             | INT(k) -> addToTuple (rl,(INT(k/a)::ti)::tl,bindList)
                                             | FLO(k) -> addToTuple (rl,(FLO((k/.(float_of_int(a))))::ti)::tl,bindList)
                                             | _ -> addToTuple (rl,(ERROR::INT(a)::N(b)::ti)::tl,bindList)
                                             )
      |(DIV::rl,(N(a)::N(b)::ti)::tl,_) -> (
                                           match (bindListHas(bindList, a),bindListHas(bindList, b)) with
                                           | (INT(k),INT(l)) -> addToTuple (rl,(INT(l/k)::ti)::tl,bindList)
                                           | (FLO(k),INT(l)) -> addToTuple (rl,(FLO((float_of_int(l)) /. k)::ti)::tl,bindList)
                                           | (FLO(k),FLO(l)) -> addToTuple (rl,(FLO(l /. k)::ti)::tl,bindList)
                                           | (INT(k),FLO(l)) -> addToTuple (rl,(FLO((l /. float_of_int(k)))::ti)::tl,bindList)
                                           | _,_ -> addToTuple (rl,(ERROR::N(a)::N(b)::ti)::tl,bindList)
                                           )
      |(DIV::rl,(FLO(a)::FLO(b)::ti)::tl,_) -> addToTuple (rl,(FLO(b /. a)::ti)::tl,bindList)
      |(DIV::rl,(N(a)::FLO(b)::ti)::tl,_) -> (
                                             match bindListHas(bindList, a) with
                                             | INT(k) -> addToTuple (rl,(FLO((b /. float_of_int(k)))::ti)::tl,bindList)
                                             | FLO(k) -> addToTuple (rl,(FLO(b /. k)::ti)::tl,bindList)
                                             | _ -> addToTuple (rl,(ERROR::N(a)::FLO(b)::ti)::tl,bindList)
                                             )
      |(DIV::rl,(FLO(a)::N(b)::ti)::tl,_) -> (
                                             match bindListHas(bindList, b) with
                                             | INT(k) -> addToTuple (rl,(FLO(float_of_int(k) /. a)::ti)::tl,bindList)
                                             | FLO(k) -> addToTuple (rl,(FLO(k /. a)::ti)::tl,bindList)
                                             | _ -> addToTuple (rl,(ERROR::FLO(a)::N(b)::ti)::tl,bindList)
                                             )
      |(DIV::rl,(FLO(a)::INT(b)::ti)::tl,_) -> addToTuple (rl,(FLO((float_of_int(b)) /. a)::ti)::tl,bindList)
      |(DIV::rl,(INT(a)::FLO(b)::ti)::tl,_) -> addToTuple (rl,(FLO(b /. (float_of_int(a)))::ti)::tl,bindList)

(*///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////*)
      (*Remainder commands*)

      |(REM::rl,(INT(a)::INT(b)::ti)::tl,_) -> addToTuple (rl,(INT(b mod a)::ti)::tl,bindList)
      |(REM::rl,(N(a)::INT(b)::ti)::tl,_) -> (
                                      match bindListHas(bindList, a) with
                                                 | INT(0) -> addToTuple (rl,(ERROR::N(a)::INT(b)::ti)::tl,bindList)
                                                 | INT(k) -> addToTuple (rl,(INT(b mod k)::ti)::tl,bindList)
                                                 | _ -> addToTuple (rl,(ERROR::N(a)::INT(b)::ti)::tl,bindList)
                                                )
      |(REM::rl,(INT(0)::N(b)::ti)::tl,_) -> addToTuple (rl,(ERROR::INT(0)::N(b)::ti)::tl,bindList)
      |(REM::rl,(INT(a)::N(b)::ti)::tl,_) -> (
                                      match bindListHas(bindList, b) with
                                                 | INT(k) -> addToTuple (rl,(INT(k mod a)::ti)::tl,bindList)
                                                 | _ -> addToTuple (rl,(ERROR::INT(a)::N(b)::ti)::tl,bindList)
                                                )
      |(REM::rl,(N(a)::N(b)::ti)::tl,_) -> (
                                      match (bindListHas(bindList, a),bindListHas(bindList, b)) with
                                                 | INT(0),_ -> addToTuple (rl,(ERROR::N(a)::N(b)::ti)::tl,bindList)
                                                 | (INT(k),INT(l)) -> addToTuple (rl,(INT(l mod k)::ti)::tl,bindList)
                                                 | _ -> addToTuple (rl,(ERROR::N(a)::N(b)::ti)::tl,bindList)
                                                )

(*///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////*)
      (*Floor commands*)
      |(ROW::rl,(FLO(a)::ti)::tl,_) -> addToTuple (rl,(INT(int_of_float(a))::ti)::tl,bindList)
      |(ROW::rl,(N(a)::ti)::tl,_) -> (
                                      match bindListHas(bindList, a) with
                                      | FLO(k) -> addToTuple (rl,(INT(int_of_float(k))::ti)::tl,bindList)
                                      | _ -> addToTuple (rl,(ERROR::N(a)::ti)::tl,bindList)
                                     )

(*///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////*)
      (*Negation commands*)
      |(NEG::rl,(INT(0)::ti)::tl,_) -> addToTuple (rl,(INT(0)::ti)::tl,bindList)
      |(NEG::rl,(INT(a)::ti)::tl,_) -> addToTuple (rl,(INT(-a)::ti)::tl,bindList)
      |(NEG::rl,(N(a)::ti)::tl,_) -> (
                                      match bindListHas(bindList, a) with
                                      | INT(0) -> addToTuple (rl,(INT(0)::ti)::tl,bindList)
                                      | INT(a) -> addToTuple (rl,(INT(-a)::ti)::tl,bindList)
                                      | _ -> addToTuple (rl,(ERROR::N(a)::ti)::tl,bindList)
                                     )

(*///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////*)
      (*Other commands*)

      |(SWAP::rl,(a::b::ti)::tl,_) -> addToTuple (rl,(b::a::ti)::tl,bindList)
      |(QUIT::_,_,_) -> constList,bindList
      |(CAT::rl,(S(a)::S(b)::ti)::tl,_) -> addToTuple(rl,(S((String.sub b 0 ((String.length b)-1))^(String.sub a 1 ((String.length a)-1)))::ti)::tl,bindList)
      |(CAT::rl,(S(a)::N(b)::ti)::tl,_) -> (
                                            match bindListHas(bindList,b) with
                                            |S(k) -> addToTuple (rl,(S((String.sub k 0 ((String.length k)-1))^(String.sub a 1 ((String.length a) -1)))::ti)::tl,bindList)
                                            |_ -> addToTuple (rl,(ERROR::S(a)::N(b)::ti)::tl,bindList)
                                           )
      |(CAT::rl,(N(a)::S(b)::ti)::tl,_) -> (
                                            match bindListHas(bindList,a) with
                                            |S(k) -> addToTuple (rl,(S((String.sub b 0 ((String.length b)-1))^(String.sub k 1 ((String.length k)-1)))::ti)::tl,bindList)
                                            |_ -> addToTuple (rl,(ERROR::N(a)::S(b)::ti)::tl,bindList)
                                           )
      |(CAT::rl,(N(a)::N(b)::ti)::tl,_) -> (
                                           match (bindListHas(bindList,a),bindListHas(bindList,b)) with
                                           |S(k),S(l) -> addToTuple (rl,(S((String.sub l 0 ((String.length l)-1))^(String.sub k 1 ((String.length k)-1)))::ti)::tl,bindList)
                                           |_ -> addToTuple (rl,(ERROR::N(a)::N(b)::ti)::tl,bindList)
                                                   )
      |(AND::rl,(BOOL(a)::BOOL(b)::ti)::tl,_) -> addToTuple(rl,(BOOL(a && b)::ti)::tl,bindList)
      |(AND::rl,(N(a)::BOOL(b)::ti)::tl,_) -> (
                                              match bindListHas(bindList,a) with
                                              |BOOL(k) -> addToTuple (rl,(BOOL(k&&b)::ti)::tl,bindList)
                                              |_ -> addToTuple (rl,(ERROR::N(a)::BOOL(b)::ti)::tl,bindList)
                                              )
      |(AND::rl,(BOOL(a)::N(b)::ti)::tl,_) -> (
                                              match bindListHas(bindList,b) with
                                              |BOOL(k) -> addToTuple (rl,(BOOL(a&&k)::ti)::tl,bindList)
                                              |_ -> addToTuple (rl,(ERROR::BOOL(a)::N(b)::ti)::tl,bindList)
                                              )
      |(AND::rl,(N(a)::N(b)::ti)::tl,_) -> (
                                           match (bindListHas(bindList,a),bindListHas(bindList,b)) with
                                           |BOOL(k),BOOL(l) -> addToTuple (rl,(BOOL(k&&l)::ti)::tl,bindList)
                                           |_ -> addToTuple (rl,(ERROR::N(a)::N(b)::ti)::tl,bindList)
                                           )
      |(OR::rl,(BOOL(a)::BOOL(b)::ti)::tl,_) -> addToTuple(rl,(BOOL(a||b)::ti)::tl,bindList)
      |(OR::rl,(N(a)::BOOL(b)::ti)::tl,_) -> (
                                              match bindListHas(bindList,a) with
                                              |BOOL(k) -> addToTuple (rl,(BOOL(k||b)::ti)::tl,bindList)
                                              |_ -> addToTuple (rl,(ERROR::N(a)::BOOL(b)::ti)::tl,bindList)
                                              )
      |(OR::rl,(BOOL(a)::N(b)::ti)::tl,_) -> (
                                             match bindListHas(bindList,b) with
                                             |BOOL(k) -> addToTuple (rl,(BOOL(a||k)::ti)::tl,bindList)
                                             |_ -> addToTuple (rl,(ERROR::BOOL(a)::N(b)::ti)::tl,bindList)
                                              )
      |(OR::rl,(N(a)::N(b)::ti)::tl,_) -> (
                                          match (bindListHas(bindList,a),bindListHas(bindList,b)) with
                                          |BOOL(k),BOOL(l) -> addToTuple (rl,(BOOL(k||l)::ti)::tl,bindList)
                                          |_ -> addToTuple (rl,(ERROR::N(a)::N(b)::ti)::tl,bindList)
                                          )
      |(NOT::rl,(BOOL(a)::ti)::tl,_) -> addToTuple(rl,(BOOL(not a)::ti)::tl,bindList)
      |(NOT::rl,(N(a)::ti)::tl,_) -> (
                                     match bindListHas(bindList,a) with
                                     |BOOL(l) -> addToTuple (rl,(BOOL(not l)::ti)::tl,bindList)
                                     |_ -> addToTuple (rl,(ERROR::N(a)::ti)::tl,bindList)
                                     )
      |(EQUAL::rl,(INT(a)::INT(b)::ti)::tl,_) -> addToTuple(rl,(BOOL(b==a)::ti)::tl,bindList)
      |(EQUAL::rl,(N(a)::INT(b)::ti)::tl,_) -> (
                                        match bindListHas(bindList,a) with
                                        |INT(l) -> addToTuple (rl,(BOOL(l==b)::ti)::tl,bindList)
                                                  |_ -> addToTuple (rl,(ERROR::N(a)::INT(b)::ti)::tl,bindList)
                                                  )
      |(EQUAL::rl,(INT(a)::N(b)::ti)::tl,_) -> (
                                        match bindListHas(bindList,b) with
                                        |INT(l) -> addToTuple (rl,(BOOL(l==a)::ti)::tl,bindList)
                                                  |_ -> addToTuple (rl,(ERROR::INT(a)::N(b)::ti)::tl,bindList)
                                                  )
      |(EQUAL::rl,(N(a)::N(b)::ti)::tl,_) -> (
                                      match (bindListHas(bindList,a),bindListHas(bindList,b)) with
                                      |INT(k),INT(l) -> addToTuple (rl,(BOOL(k==l)::ti)::tl,bindList)
                                                      |_ -> addToTuple (rl,(ERROR::N(a)::N(b)::ti)::tl,bindList)
                                                     )
      |(LESS::rl,(INT(a)::INT(b)::ti)::tl,_) -> addToTuple(rl,(BOOL(b<a)::ti)::tl,bindList)
      |(LESS::rl,(N(a)::INT(b)::ti)::tl,_) -> (
                                       match bindListHas(bindList,a) with
                                       |INT(l) -> addToTuple (rl,(BOOL(b<l)::ti)::tl,bindList)
                                                  |_ -> addToTuple (rl,(ERROR::N(a)::INT(b)::ti)::tl,bindList)
                                                 )
      |(LESS::rl,(INT(a)::N(b)::ti)::tl,_) -> (
                                              match bindListHas(bindList,b) with
                                              |INT(l) -> addToTuple (rl,(BOOL(l<a)::ti)::tl,bindList)
                                              |_ -> addToTuple (rl,(ERROR::INT(a)::N(b)::ti)::tl,bindList)
                                              )
      |(LESS::rl,(N(a)::N(b)::ti)::tl,_) -> (
                                            match (bindListHas(bindList,a),bindListHas(bindList,b)) with
                                            |INT(k),INT(l) -> addToTuple (rl,(BOOL(l<k)::ti)::tl,bindList)
                                            |_ -> addToTuple (rl,(ERROR::N(a)::N(b)::ti)::tl,bindList)
                                            )
      |(BIND::rl,(INT(a)::N(b)::ti)::tl,(lh)::lt) -> addToTuple(rl,(UNIT::ti)::tl,((N(b),INT(a))::lh)::lt) (*TODO logical issue with heap here*)
      |(BIND::rl,(BOOL(a)::N(b)::ti)::tl,(lh)::lt) -> addToTuple(rl,(UNIT::ti)::tl,((N(b),BOOL(a))::lh)::lt)(*TODO logical issue with heap here*)
      |(BIND::rl,(S(a)::N(b)::ti)::tl,(lh)::lt) -> addToTuple(rl,(UNIT::ti)::tl,((N(b),S(a))::lh)::lt) (*TODO logical issue with heap here*)
      |(BIND::rl,(UNIT::N(b)::ti)::tl,(lh)::lt) -> addToTuple(rl,(UNIT::ti)::tl,((N(b),UNIT)::lh)::lt) (*TODO logical issue with heap here*)
      |(BIND::rl,(FUNCT(a,b,c,d)::N(e)::ti)::tl,(lh)::lt) -> addToTuple(rl,(UNIT::ti)::tl,((N(e),FUNCT(a,b,c,d))::lh)::lt) (*TODO logical issue with heap here*)
      |(BIND::rl,(N(a)::N(b)::ti)::tl,(lh)::lt) -> (
                                                    match (bindListHas(bindList,a)) with
                                                    |ERROR -> addToTuple(rl,(ERROR::N(a)::N(b)::ti)::tl,(lh)::lt)
                                                    | c -> addToTuple(rl,(UNIT::ti)::tl,((N(b),c)::lh)::lt)
                                                   )
                                                    (*TODO logical issue with heap here*)
      |(IF::rl,(a::b::BOOL(c)::ti)::tl,_) -> (
                                     match c with
                                     |true -> addToTuple(rl,(a::ti)::tl,bindList)
                                     |false -> addToTuple(rl,(b::ti)::tl,bindList)
                                     )
      |(IF::rl,(a::b::N(c)::ti)::tl,_) -> (
                                     match bindListHas(bindList,c) with
                                     |BOOL(true) -> addToTuple(rl,(a::ti)::tl,bindList)
                                     |BOOL(false) -> addToTuple(rl,(b::ti)::tl,bindList)
                                     |_ -> addToTuple(rl,(ERROR::ti)::tl,bindList)
                                  )
      |LET::rl,hd::tl,_ -> addToTuple(rl,[]::constList,[]::bindList)
      |END::rl,hd::nexth::tl,bindh::bindt -> ( match hd with
                             |a::b -> addToTuple(rl, (a::nexth)::tl,bindt)
                             |[] -> addToTuple(rl, (nexth)::tl,bindt)
                           )
      |_::rl,(hd)::tl,_ -> addToTuple(rl,(ERROR::hd)::tl,bindList)
      |_,_,_ -> constList,bindList
in

let lettersList =['A';'B';'C';'D';'E';'F';'G';'H';'I';'J';'K';'L';'M';'N';'O';'P';'Q';'R';'S';'T';'U';'V';'W';'X';'Y';'Z';'a';'b';'c';'d';'e';'f';'g';'h';'i';'j';'k';'l';'m';'n';'o';'p';'q';'r';'s';'t';'u';'v';'w';'x';'y';'z';'_'] in
let rec nvalid name lettersList =
      match lettersList with
      |[] -> PUSH(ERROR)
      |hd::tl -> if String.contains (String.sub name 0 1) hd then  PUSHN(name) else nvalid name tl

in


let rec makeList  (acc,commandList,constList,lettersList,bindList) =
    match acc with
      | []-> addToTuple(commandList,constList,bindList)
      | hd::tl -> (
                  match String.split_on_char ' ' hd with
                  |"pushi"::rl::trash ->(try makeList(tl,PUSHI(int_of_string rl)::commandList,constList,lettersList,bindList) with
                                  | Failure(int_of_string) -> makeList(tl,PUSH(ERROR)::commandList,constList,lettersList,bindList)
                                 )
                  |"pushf"::rl::trash ->(try makeList(tl,PUSHF(float_of_string rl)::commandList,constList,lettersList,bindList) with
                                  | Failure(float_of_string) -> makeList(tl,PUSH(ERROR)::commandList,constList,lettersList,bindList)
                                 )
                  |"pushb"::rl::trash ->(match rl with
                                  |":true:" -> makeList(tl,PUSHB(true)::commandList,constList,lettersList,bindList)
                                  |":false:" -> makeList(tl,PUSHB(false)::commandList,constList,lettersList,bindList)
                                  |_ -> makeList(tl,PUSH(ERROR)::commandList,constList,lettersList,bindList)
                                  )
                  |"pushs"::rl -> ( if (Char.equal (String.concat " " rl).[0] '"') && (Char.equal(String.concat " " rl).[String.length(String.concat " " rl)-1] '"')
                                    then makeList(tl,PUSHS(String.concat " " rl)::commandList,constList,lettersList,bindList) else
                                    makeList(tl,PUSH(ERROR)::commandList,constList,lettersList,bindList)  )
                  |"pushn"::rl::trash -> makeList(tl,(nvalid rl lettersList)::commandList,constList,lettersList,bindList)
                  |"push"::rl::trash ->  (
                                  match (rl) with
                                  | ":error:" -> makeList(tl,PUSH(ERROR)::commandList, constList,lettersList,bindList)
                                  | ":unit:" -> makeList(tl,PUSH(UNIT)::commandList, constList,lettersList,bindList)
                                  | _ -> makeList(tl,PUSH(ERROR)::commandList,constList,lettersList,bindList)
                    )
                  |"pop"::trash -> makeList(tl,POP::commandList,constList,lettersList,bindList)
                  |"add"::trash -> makeList(tl,ADD::commandList,constList,lettersList,bindList)
                  |"sub"::trash -> makeList(tl,SUB::commandList,constList,lettersList,bindList)
                  |"mul"::trash -> makeList(tl,MUL::commandList,constList,lettersList,bindList)
                  |"div"::trash -> makeList(tl,DIV::commandList,constList,lettersList,bindList)
                  |"rem"::trash -> makeList(tl,REM::commandList,constList,lettersList,bindList)
                  |"floor"::trash -> makeList(tl,ROW::commandList,constList,lettersList,bindList)
                  |"neg"::trash -> makeList(tl,NEG::commandList,constList,lettersList,bindList)
                  |"swap"::trash -> makeList(tl,SWAP::commandList,constList,lettersList,bindList)
                  |"quit"::trash -> makeList(tl,QUIT::commandList,constList,lettersList,bindList)
                  |"cat"::trash -> makeList(tl,CAT::commandList,constList,lettersList,bindList)
                  |"and"::trash -> makeList(tl,AND::commandList,constList,lettersList,bindList)
                  |"or"::trash -> makeList(tl,OR::commandList,constList,lettersList,bindList)
                  |"not"::trash -> makeList(tl,NOT::commandList,constList,lettersList,bindList)
                  |"equal"::trash -> makeList(tl,EQUAL::commandList,constList,lettersList,bindList)
                  |"lessThan"::trash -> makeList(tl,LESS::commandList,constList,lettersList,bindList)
                  |"bind"::trash -> makeList(tl,BIND::commandList,constList,lettersList,bindList)
                  |"if"::trash -> makeList(tl,IF::commandList,constList,lettersList,bindList)
                  |"let"::trash -> makeList(tl,LET::commandList,constList,lettersList,bindList)
                  |"end"::trash -> makeList(tl,END::commandList,constList,lettersList,bindList)
                  |"fun"::name::param::trash -> makeList(tl,FUN(name,param)::commandList,constList,lettersList,bindList)
                  |"return"::trash -> makeList(tl,RETURN::commandList,constList,lettersList,bindList)
                  |"call"::trash -> makeList(tl,CALL::commandList,constList,lettersList,bindList)
                  |"funEnd"::trash -> makeList(tl,FUNEND::commandList,constList,lettersList,bindList)
                  |"inOutFun"::name::param::trash -> makeList(tl,INOUTFUN(name,param)::commandList,constList,lettersList,bindList)
                  |_-> makeList(tl,PUSH(ERROR)::commandList,constList,lettersList,bindList)
                  )
in
writeOut(makeList(acc,[],[[]],lettersList,[[]]))
;;
