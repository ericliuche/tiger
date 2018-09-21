type pos = int
type lexresult = Tokens.token

(* Error handling *)
val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
fun err(p1, p2) = ErrorMsg.error p1

(* Increments the line count and tracks the current lexer position *)
fun handleNewline(yypos) = (lineNum := !lineNum + 1; linePos := yypos :: !linePos)
    
(* Finds the column number for the given position starting from the given line number *)
fun colNumber(yypos, startPosList, lineNumber) =
    case startPosList of
        (a::rest) => if a < yypos then (yypos - a) else colNumber(yypos, rest, lineNumber - 1)
    |   _ => 0

(* Gets the current line and column numbers for the parser *)
fun curLinePos(yypos) =
    (!lineNum, colNumber(yypos, !linePos, !lineNum))



(* Converts the given string representation of an integer to an integer *)
fun atoi(s) = foldl
    (fn (digit, sum) => (10 * sum) + (ord(digit) - ord(#"0")))
    (0)
    (explode(s))


(* The depth of nested comments that the lexer is currently at *)
val commentDepth = ref 0

(* Handles the start of a new potentially nested comment *)
fun startComment() =
    commentDepth := !commentDepth + 1

(* Handles the end of a potentially nested comment *)
fun endComment(yypos) =
    commentDepth := !commentDepth - 1    

(* Ensures that newlines within a string literal are accounted for in the lexer position *)
fun handleStringLiteral(text, yypos) = 
    let
        val idxs = List.tabulate(size(text), (fn n => n))
        val zippedText = ListPair.zip(idxs, explode(text))
    in
        map (fn (idx, char) =>
            if (char = #"\n") then
                (lineNum := !lineNum + 1; linePos := (yypos + idx) :: !linePos)
            else ())
            (zippedText)
    end

(* Tracks if the lexer is currently within a string literal *)
val inString = ref false

(* Controls whether the lexer is currently within a string literal *)
fun beginString() = inString := true
fun endString() = inString := false


(* Handles the EOF and errors if it is within a comment *)
fun eof() =
    let val pos = hd(!linePos) in
        if !commentDepth > 0 then
            (ErrorMsg.error pos "Unexpected end of file inside of a comment")
        else if !inString then
            (ErrorMsg.error pos "Unexpected end of file inside string literal")
        else
            ();
        Tokens.EOF(curLinePos(pos))
    end


%%

digit=[0-9];
letter=[a-zA-Z];
ws=[ \t];

nonprintable=[ \n\t\f];
ctrlChar=[A-Z@^_]|"\\"|"["|"]";
asciiCode=([01]{digit}{digit})|(2[0-4]{digit})|(25[0-5]);
escapeSequence="\\"("n"|"t"|"\\"|("^"{ctrlChar})|{asciiCode}|"\""|({nonprintable}+"\\"));

%s COMMENT STRING ERROR;

%%


<INITIAL>\n    => (handleNewline(yypos); continue());
<INITIAL>{ws}  => (continue());

<INITIAL>"type"      => (Tokens.TYPE(curLinePos(yypos)));
<INITIAL>"var"       => (Tokens.VAR(curLinePos(yypos)));
<INITIAL>"function"  => (Tokens.FUNCTION(curLinePos(yypos)));
<INITIAL>"break"     => (Tokens.BREAK(curLinePos(yypos)));
<INITIAL>"of"        => (Tokens.OF(curLinePos(yypos)));
<INITIAL>"end"       => (Tokens.END(curLinePos(yypos)));
<INITIAL>"in"        => (Tokens.IN(curLinePos(yypos)));
<INITIAL>"nil"       => (Tokens.NIL(curLinePos(yypos)));
<INITIAL>"let"       => (Tokens.LET(curLinePos(yypos)));
<INITIAL>"do"        => (Tokens.DO(curLinePos(yypos)));
<INITIAL>"to"        => (Tokens.TO(curLinePos(yypos)));
<INITIAL>"for"       => (Tokens.FOR(curLinePos(yypos)));
<INITIAL>"while"     => (Tokens.WHILE(curLinePos(yypos)));
<INITIAL>"else"      => (Tokens.ELSE(curLinePos(yypos)));
<INITIAL>"then"      => (Tokens.THEN(curLinePos(yypos)));
<INITIAL>"if"        => (Tokens.IF(curLinePos(yypos)));
<INITIAL>"array of"  => (Tokens.ARRAY(curLinePos(yypos)));

<INITIAL>":="        => (Tokens.ASSIGN(curLinePos(yypos)));
<INITIAL>"|"         => (Tokens.OR(curLinePos(yypos)));
<INITIAL>"&"         => (Tokens.AND(curLinePos(yypos)));
<INITIAL>">="        => (Tokens.GE(curLinePos(yypos)));
<INITIAL>">"         => (Tokens.GT(curLinePos(yypos)));
<INITIAL>"<="        => (Tokens.LE(curLinePos(yypos)));
<INITIAL>"<"         => (Tokens.LT(curLinePos(yypos)));
<INITIAL>"<>"        => (Tokens.NEQ(curLinePos(yypos)));
<INITIAL>"="         => (Tokens.EQ(curLinePos(yypos)));
<INITIAL>"/"         => (Tokens.DIVIDE(curLinePos(yypos)));
<INITIAL>"*"         => (Tokens.TIMES(curLinePos(yypos)));
<INITIAL>"-"         => (Tokens.MINUS(curLinePos(yypos)));
<INITIAL>"+"         => (Tokens.PLUS(curLinePos(yypos)));
<INITIAL>"."         => (Tokens.DOT(curLinePos(yypos)));
<INITIAL>"}"         => (Tokens.RBRACE(curLinePos(yypos)));
<INITIAL>"{"         => (Tokens.LBRACE(curLinePos(yypos)));
<INITIAL>"]"         => (Tokens.RBRACK(curLinePos(yypos)));
<INITIAL>"["         => (Tokens.LBRACK(curLinePos(yypos)));
<INITIAL>")"         => (Tokens.RPAREN(curLinePos(yypos)));
<INITIAL>"("         => (Tokens.LPAREN(curLinePos(yypos)));
<INITIAL>":"         => (Tokens.COLON(curLinePos(yypos)));
<INITIAL>";"         => (Tokens.SEMICOLON(curLinePos(yypos)));
<INITIAL>","         => (Tokens.COMMA(curLinePos(yypos)));

<INITIAL>"/*"        => (YYBEGIN COMMENT; startComment(); continue());
<INITIAL>"*/"        => (ErrorMsg.error yypos ("Unexpected end of comment"); YYBEGIN ERROR; continue());
<COMMENT>"/*"        => (startComment(); continue());
<COMMENT>"*/"        => (case !commentDepth of
                            0 => (ErrorMsg.error yypos ("illegal end of comment"); YYBEGIN ERROR; continue())
                        |   1 => (endComment(); YYBEGIN INITIAL; continue())
                        |   _ => (endComment(); continue()));
<COMMENT>"\n"        => (handleNewline(yypos); continue());                        

<COMMENT>.           => (continue());


<INITIAL>"\""                       => (YYBEGIN STRING; beginString(); continue());
<STRING>([^\"\\]|{escapeSequence})* => (let val startLineNum = !lineNum in
                                            handleStringLiteral(yytext, yypos);
                                            Tokens.STRING(
                                                yytext,
                                                startLineNum,
                                                colNumber(yypos, !linePos, startLineNum))
                                        end);
<STRING>"\""                        => (YYBEGIN INITIAL; endString(); continue());
<STRING>.            => (ErrorMsg.error yypos ("illegal charater in string"); YYBEGIN ERROR; continue());
<INITIAL>"\"\""      => (Tokens.STRING("", !lineNum, colNumber(yypos, !linePos, !lineNum)));


<INITIAL>{digit}+  => (Tokens.INT(atoi(yytext), !lineNum, colNumber(yypos, !linePos, !lineNum)));

<INITIAL>{letter}({letter}|{digit})*  => (Tokens.ID(yytext, !lineNum, colNumber(yypos, !linePos, !lineNum)));


<ERROR>.    => (continue());
<INITIAL>.  => (ErrorMsg.error yypos ("illegal character " ^ yytext); YYBEGIN ERROR; continue());
