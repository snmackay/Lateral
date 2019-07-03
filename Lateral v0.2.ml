(* Lateral Beta V0.2
 * Sean Mackay
 * snmackay@buffalo.edu
 * 3/30/19                          *)

type const = BOOL of bool| INT of int | ERROR | S of string | N of string | UNIT
type command = PUSH of const | PUSHI of int | PUSHS of string | PUSHN of string | PUSHB of bool | POP | ADD | SUB | MUL | DIV | REM | NEG | SWAP | QUIT | CAT | AND | OR | NOT | EQUAL | LESS | BIND | IF | LET | END


let interpreter (inFile,outFile) :unit=

let ic = open_in inFile in

let oc = open_out outFile in

let rec loop_read acc =

    try

        let l = input_line ic in loop_read (l::acc)
    with

    | End_of_file -> acc in

let rec acc =loop_read [] in

let rec writeOut (constList: const list list) : unit  =
    match constList with
      |[]::back -> writeOut back
      |front::back -> (
                 match front with
                 |hd::tl -> (
                          match hd with
                          |INT(a) -> (
                              Printf.fprintf oc "%s\n" (string_of_int a);
                              writeOut ((tl)::back) )
                          |BOOL(a) -> (
                              Printf.fprintf oc "%s\n" (":"^(string_of_bool a)^":");
                              writeOut ((tl)::back) )
                          |S(a) -> (
                              Printf.fprintf oc "%s\n" (String.sub a 1 ((String.length a)-2));
                              writeOut ((tl)::back) )
                          |N(a) -> (
                              Printf.fprintf oc "%s\n" a;
                              writeOut ((tl)::back) )
                          |ERROR -> (
                              Printf.fprintf oc "%s\n" ":error:";
                              writeOut ((tl)::back))
                          |UNIT -> (
                              Printf.fprintf oc "%s\n" ":unit:";
                              writeOut ((tl)::back ))

                          )
                 |[] -> writeOut back
                 )
     |_ -> ()


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
               |(N(a),N(rl))::tr -> bindListHas(bindList,rl)
               | _ -> bindListHas(tl,name)
               )
in



let rec addToTuple (commandList,(constList :const list list),bindList) =
    match commandList,constList,bindList with
      |(PUSHB(a)::rl,hd::tl,_) -> addToTuple (rl,(BOOL(a)::hd)::tl,bindList)
      |(PUSHI(a)::rl,(aa)::tl,_) -> addToTuple (rl,(INT(a)::aa)::tl,bindList)
      |(PUSHS(a)::rl,(aa)::tl,_) -> addToTuple (rl,(S(a)::aa)::tl,bindList)
      |(PUSHN(a)::rl,(aa)::tl,_) -> addToTuple (rl,(N(a)::aa)::tl,bindList)
      |(PUSH(a)::rl,(aa)::tl,_) -> addToTuple (rl,(a::aa)::tl,bindList)

      |(POP::rl,[]::tl,_)-> addToTuple (rl,(ERROR::[])::tl,bindList)
      |(POP::rl,(hi::ti)::tl,_)-> addToTuple (rl,(ti)::tl,bindList)
      (*TODO REREAD LOGIC BEHIND HEAP COMMANDS*)
      |(ADD::rl,(INT(a)::INT(b)::ti)::tl,_) -> addToTuple (rl,(INT(a+b)::ti)::tl,bindList)
      |(ADD::rl,(N(a)::INT(b)::ti)::tl,_) -> (
                                             match bindListHas(bindList, a) with
                                             | INT(k) -> addToTuple (rl,(INT(k+b)::ti)::tl,bindList)
                                             | _ -> addToTuple (rl,(ERROR::N(a)::INT(b)::ti)::tl,bindList)
                                             )
      |(ADD::rl,(INT(a)::N(b)::ti)::tl,_) -> (
                                             match bindListHas(bindList, b) with
                                             | INT(k) -> addToTuple (rl,(INT(k+a)::ti)::tl,bindList)
                                                 | _ -> addToTuple (rl,(ERROR::INT(a)::N(b)::ti)::tl,bindList)
                                                )
      |(ADD::rl,(N(a)::N(b)::ti)::tl,_) -> (
                                           match (bindListHas(bindList, a),bindListHas(bindList, b)) with
                                           | (INT(k),INT(l)) -> addToTuple (rl,(INT(k+l)::ti)::tl,bindList)
                                           | _,_ -> addToTuple (rl,(ERROR::N(a)::N(b)::ti)::tl,bindList)
                                                )

      |(SUB::rl,(INT(a)::INT(b)::ti)::tl,_) -> addToTuple (rl,(INT(b-a)::ti)::tl,bindList)
      |(SUB::rl,(N(a)::INT(b)::ti)::tl,_) -> (
                                      match bindListHas(bindList, a) with
                                      | INT(k) -> addToTuple (rl,(INT(b-k)::ti)::tl,bindList)
                                                 | _ -> addToTuple (rl,(ERROR::N(a)::INT(b)::ti)::tl,bindList)
                                                )
      |(SUB::rl,(INT(a)::N(b)::ti)::tl,_) -> (
                                      match bindListHas(bindList, b) with
                                      | INT(k) -> addToTuple (rl,(INT(k-a)::ti)::tl,bindList)
                                                 | _ -> addToTuple (rl,(ERROR::INT(a)::N(b)::ti)::tl,bindList)
                                                )
      |(SUB::rl,(N(a)::N(b)::ti)::tl,_) -> (
                                      match (bindListHas(bindList, a),bindListHas(bindList, b)) with
                                    | (INT(k),INT(l)) -> addToTuple (rl,(INT(l-k)::ti)::tl,bindList)
                                    | _,_ -> addToTuple (rl,(ERROR::N(a)::N(b)::ti)::tl,bindList)
                                                )

      |(MUL::rl,(INT(a)::INT(b)::ti)::tl,_) -> addToTuple (rl,(INT(b*a)::ti)::tl,bindList)
      |(MUL::rl,(N(a)::INT(b)::ti)::tl,_) -> (
                                      match bindListHas(bindList, a) with
                                      | INT(k) -> addToTuple (rl,(INT(b*k)::ti)::tl,bindList)
                                                 | _ -> addToTuple (rl,(ERROR::N(a)::INT(b)::ti)::tl,bindList)
                                                )
      |(MUL::rl,(INT(a)::N(b)::ti)::tl,_) -> (
                                      match bindListHas(bindList, b) with
                                      | INT(k) -> addToTuple (rl,(INT(k*a)::ti)::tl,bindList)
                                                 | _ -> addToTuple (rl,(ERROR::INT(a)::N(b)::ti)::tl,bindList)
                                                )
      |(MUL::rl,(N(a)::N(b)::ti)::tl,_) -> (
                                      match (bindListHas(bindList, a),bindListHas(bindList, b)) with
                                      | (INT(k),INT(l)) -> addToTuple (rl,(INT(l*k)::ti)::tl,bindList)
                                                 | _ -> addToTuple (rl,(ERROR::N(a)::N(b)::ti)::tl,bindList)
                                                )

      |(DIV::rl,(INT(0)::INT(b)::ti)::tl,_) -> addToTuple (rl,(ERROR::INT(0)::INT(b)::ti)::constList,bindList)
      |(DIV::rl,(N(a)::INT(b)::ti)::tl,_) -> (
                                             match bindListHas(bindList, a) with
                                             | INT(0) -> addToTuple (rl,(ERROR::N(a)::INT(b)::ti)::tl,bindList)
                                             | INT(k) -> addToTuple (rl,(INT(b/k)::ti)::tl,bindList)
                                             | _ -> addToTuple (rl,(ERROR::N(a)::INT(b)::ti)::tl,bindList)
                                             )
      |(DIV::rl,(INT(0)::N(b)::ti)::tl,_) -> addToTuple (rl,(ERROR::INT(0)::N(b)::ti)::tl,bindList)
      |(DIV::rl,(INT(a)::N(b)::ti)::tl,_) -> (
                                      match bindListHas(bindList, b) with
                                      | INT(k) -> addToTuple (rl,(INT(k/a)::ti)::tl,bindList)
                                                 | _ -> addToTuple (rl,(ERROR::INT(a)::N(b)::ti)::tl,bindList)
                                                )
      |(DIV::rl,(N(a)::N(b)::ti)::tl,_) -> (
                                      match (bindListHas(bindList, a),bindListHas(bindList, b)) with
                                      | (INT(0),INT(l)) -> addToTuple (rl,(ERROR::N(a)::N(b)::ti)::tl,bindList)
                                      | (INT(k),INT(l)) -> addToTuple (rl,(INT(l/k)::ti)::tl,bindList)
                                      | _ -> addToTuple (rl,(ERROR::N(a)::N(b)::ti)::tl,bindList)
                                                )
      |(DIV::rl,(INT(a)::INT(b)::ti)::tl,_) -> addToTuple (rl,(INT(b/a)::ti)::tl,bindList)

      |(REM::rl,(INT(0)::INT(b)::ti)::tl,_) -> addToTuple (rl,(ERROR::INT(0)::INT(b)::ti)::tl,bindList)
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

      |(NEG::rl,(INT(0)::ti)::tl,_) -> addToTuple (rl,(INT(0)::ti)::tl,bindList)
      |(NEG::rl,(INT(a)::ti)::tl,_) -> addToTuple (rl,(INT(-a)::ti)::tl,bindList)
      |(NEG::rl,(N(a)::ti)::tl,_) -> (
                                      match bindListHas(bindList, a) with
                                      | INT(0) -> addToTuple (rl,(INT(0)::ti)::tl,bindList)
                                      | INT(a) -> addToTuple (rl,(INT(-a)::ti)::tl,bindList)
                                      | _ -> addToTuple (rl,(ERROR::N(a)::ti)::tl,bindList)
                                     )

      |(SWAP::rl,(a::b::ti)::tl,_) -> addToTuple (rl,(b::a::ti)::tl,bindList)
      |(QUIT::_,_,_) -> writeOut constList

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
      |_,_,_ ->()

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
                  |_-> makeList(tl,PUSH(ERROR)::commandList,constList,lettersList,bindList)
                  )
in



makeList(acc,[],[[]],lettersList,[[]])
;;
