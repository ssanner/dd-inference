package prob.bn.parser;

%%
%unicode
%char
%line
%type Symbol
%function nextToken
%eofval{  
	return new Symbol(Symbol.EOF); 
%eofval}
%{
public int yyline() { return yyline; } 
%}
ALPHA=[A-Za-z:_-.%]
DIGIT=[0-9]
WHITE_SPACE_CHAR=[\r\n\ \t\b\012]
QUOTED_STRING=\"[^\"]*\"
SLASH_COMMENT_TEXT=.*[\r\n]
%%
"//"{SLASH_COMMENT_TEXT} { return new Symbol(Symbol.COMMENT, yytext(), yyline()); }
"true" { return new Symbol(Symbol.TRUE, null, yyline()); }
"false" { return new Symbol(Symbol.FALSE, null, yyline()); }
";" { return new Symbol(Symbol.SEMI, null, yyline()); }
"!" { return new Symbol(Symbol.BANG, null, yyline()); }
"?" { return new Symbol(Symbol.QST, null, yyline()); }
"+" { return new Symbol(Symbol.PLUS, null, yyline()); }
"*" { return new Symbol(Symbol.TIMES, null, yyline()); }
"(" { return new Symbol(Symbol.LPAREN, null, yyline()); }
")" { return new Symbol(Symbol.RPAREN, null, yyline()); }
"%" { return new Symbol(Symbol.MOD, null, yyline()); }
"," { return new Symbol(Symbol.COMMA, null, yyline()); }
"[" { return new Symbol(Symbol.LBRACK, null, yyline()); }
"]" { return new Symbol(Symbol.RBRACK, null, yyline()); }
"<=" { return new Symbol(Symbol.LESSEQ, null, yyline()); }
"<" { return new Symbol(Symbol.LESS, null, yyline()); }
"#" { return new Symbol(Symbol.COUNT, null, yyline()); }
">=" { return new Symbol(Symbol.GREATEREQ, null, yyline()); }
">" { return new Symbol(Symbol.GREATER, null, yyline()); }
"^" { return new Symbol(Symbol.AND, null, yyline()); }
"~" { return new Symbol(Symbol.NOT, null, yyline()); }
"|" { return new Symbol(Symbol.OR, null, yyline()); }
"=>" { return new Symbol(Symbol.IMPLY, null, yyline()); }
"<=>" { return new Symbol(Symbol.EQUIV, null, yyline()); }
"~=" { return new Symbol(Symbol.NEQUAL, null, yyline()); }
"=" { return new Symbol(Symbol.EQUAL, null, yyline()); }
"/" { return new Symbol(Symbol.DIV, null, yyline()); }
"{" { return new Symbol(Symbol.LCBRACE, null, yyline()); }
"}" { return new Symbol(Symbol.RCBRACE, null, yyline()); }

{DIGIT}+"."{DIGIT}+ { return new Symbol(Symbol.DOUBLE, new Double(yytext()), yyline()); }
{DIGIT}+"."{DIGIT}+("e"|"E")("+"|"-")?{DIGIT}+ { return new Symbol(Symbol.DOUBLE, new Double(yytext()), yyline()); }
{DIGIT}+("e"|"E")("+"|"-")?{DIGIT}+ { return new Symbol(Symbol.DOUBLE, new Double(yytext()), yyline()); }
{DIGIT}+ { return new Symbol(Symbol.INTEGER, new Integer(yytext()), yyline()); }
{QUOTED_STRING} { return new Symbol(Symbol.IDENT, yytext(), yyline()); }
({ALPHA}|{DIGIT}|"."|"-"|"_"|"%")* { return new Symbol(Symbol.IDENT, yytext(), yyline()); }
{WHITE_SPACE_CHAR}+ { /* ignore white space. */ }
. { System.err.println("Illegal character: "+yytext()+":ln:" + yyline()); System.exit(1); }

"-" { return new Symbol(Symbol.MINUS, null, yyline()); }
