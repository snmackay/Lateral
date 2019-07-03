(* Lateral v0.1
 * Derived from a school project
 * Sean Mackay
 * snmackay@buffalo.edu
 * 3/30/19                          *)

type const = BOOL of bool| INT of int | ERROR | S of string | N of string | UNIT
type command = PUSH of const | PUSHI of int | PUSHS of string | PUSHN of string | PUSHB of bool | POP | ADD | SUB | MUL | DIV | REM | NEG | SWAP | QUIT

let interpreter (inFile,outFile) :unit=

let ic = open_in inFile in

let oc = open_out outFile in

let rec loop_read acc =

    try

        let l = input_line ic in loop_read (l::acc)
    with

    | End_of_file -> acc in

let rec acc =loop_read [] in

let rec writeOut constList :unit  =
    match constList with
      |[] -> ()
      |hd::tl -> (
                 match hd with
                 |INT(a) -> (
                         Printf.fprintf oc "%s\n" (string_of_int a);
                             writeOut tl )
                 |BOOL(a) -> (
                         Printf.fprintf oc "%s\n" (":"^(string_of_bool a)^":");
                              writeOut tl )
                 |S(a) -> (
                         Printf.fprintf oc "%s\n" (String.sub a 1 ((String.length a)-2));
                           writeOut tl )
                 |N(a) -> (
                         Printf.fprintf oc "%s\n" a;
                           writeOut tl )
                 |ERROR -> (
                         Printf.fprintf oc "%s\n" ":error:";
                            writeOut tl )
                 |UNIT -> (
                         Printf.fprintf oc "%s\n" ":unit:";
                           writeOut tl )
                 )
in

let rec addToTuple (commandList,constList) =
    match commandList,constList with
      |(PUSHB(a)::rl,_) -> addToTuple (rl,BOOL(a)::constList)
      |(PUSHI(a)::rl,_) -> addToTuple (rl,INT(a)::constList)
      |(PUSHS(a)::rl,_) -> addToTuple (rl,S(a)::constList)
      |(PUSHN(a)::rl,_) -> addToTuple (rl,N(a)::constList)
      |(PUSH(a)::rl,_) -> addToTuple (rl,a::constList)
      |(POP::rl,[])-> addToTuple (rl,ERROR::constList)
      |(POP::rl,hd::tl)-> addToTuple (rl,tl)
      |(ADD::rl,INT(a)::INT(b)::tl) -> addToTuple (rl,INT(a+b)::tl)
      |(SUB::rl,INT(a)::INT(b)::tl) -> addToTuple (rl,INT(b-a)::tl)
      |(MUL::rl,INT(a)::INT(b)::tl) -> addToTuple (rl,INT(b*a)::tl)
      |(DIV::rl,INT(0)::INT(b)::tl) -> addToTuple (rl,ERROR::constList)
      |(DIV::rl,INT(a)::INT(b)::tl) -> addToTuple (rl,INT(b/a)::tl)
      |(REM::rl,INT(0)::INT(b)::tl) -> addToTuple (rl,ERROR::constList)
      |(REM::rl,INT(a)::INT(b)::tl) -> addToTuple (rl,INT(b mod a)::tl)
      |(NEG::rl,INT(0)::tl) -> addToTuple (rl,INT(0)::tl)
      |(NEG::rl,INT(a)::tl) -> addToTuple (rl,INT(-a)::tl)
      |(SWAP::rl,a::b::tl) -> addToTuple (rl,b::a::tl)
      |(QUIT::_,hd::tl) -> writeOut constList
      |hd::tl,_ -> addToTuple(tl,ERROR::constList)
      |_,_ -> ()


in

let lettersList =['A';'B';'C';'D';'E';'F';'G';'H';'I';'J';'K';'L';'M';'N';'O';'P';'Q';'R';'S';'T';'U';'V';'W';'X';'Y';'Z';'a';'b';'c';'d';'e';'f';'g';'h';'i';'j';'k';'l';'m';'n';'o';'p';'q';'r';'s';'t';'u';'v';'w';'x';'y';'z';'_'] in
let rec nvalid name lettersList =
      match lettersList with
      |[] -> PUSH(ERROR)
      |hd::tl -> if String.contains (String.sub name 0 1) hd then  PUSHN(name) else nvalid name tl

in


let rec makeList  (acc,commandList,constList,lettersList) =
    match acc with
      | []-> addToTuple(commandList,constList)
      | hd::tl -> (
                  match String.split_on_char ' ' hd with
                  |"pushi"::rl::trash ->(try makeList(tl,PUSHI(int_of_string rl)::commandList,constList,lettersList) with
                                  | Failure(int_of_string) -> makeList(tl,PUSH(ERROR)::commandList,constList,lettersList)

                                 )
                  |"pushb"::rl::trash ->(match rl with
                                  |":true:" -> makeList(tl,PUSHB(true)::commandList,constList,lettersList)
                                  |":false:" -> makeList(tl,PUSHB(false)::commandList,constList,lettersList)
                                  |_ -> makeList(tl,PUSH(ERROR)::commandList,constList,lettersList)
                                  )
                  |"pushs"::rl -> (if String.index (String.concat " " rl) '"'== 0 &&
                                   String.rindex (String.concat " " rl) '"'==(String.length(String.concat " " rl))-1 then
                                    makeList(tl,PUSHS(String.concat " " rl)::commandList,constList,lettersList) else
                                    makeList(tl,PUSH(ERROR)::commandList,constList,lettersList)
                                    )
                  |"pushn"::rl::trash -> makeList(tl,(nvalid rl lettersList)::commandList,constList,lettersList)
                  |"push"::rl::trash ->  (
                                  match (rl) with
                                  | ":error:" -> makeList(tl,PUSH(ERROR)::commandList, constList,lettersList)
                                  | ":unit:" -> makeList(tl,PUSH(UNIT)::commandList, constList,lettersList)
                                  | _ -> makeList(tl,PUSH(ERROR)::commandList,constList,lettersList)
                    )
                  |"pop"::trash -> makeList(tl,POP::commandList,constList,lettersList)
                  |"add"::trash -> makeList(tl,ADD::commandList,constList,lettersList)
                  |"sub"::trash -> makeList(tl,SUB::commandList,constList,lettersList)
                  |"mul"::trash -> makeList(tl,MUL::commandList,constList,lettersList)
                  |"div"::trash -> makeList(tl,DIV::commandList,constList,lettersList)
                  |"rem"::trash -> makeList(tl,REM::commandList,constList,lettersList)
                  |"neg"::trash -> makeList(tl,NEG::commandList,constList,lettersList)
                  |"swap"::trash -> makeList(tl,SWAP::commandList,constList,lettersList)
                  |"quit"::trash -> makeList(tl,QUIT::commandList,constList,lettersList)
                  |_-> makeList(tl,PUSH(ERROR)::commandList,constList,lettersList)
                  )
in

makeList(acc,[],[],lettersList)
;;
interpreter("inputUser.txt","outputUser.txt")
