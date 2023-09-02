Whitespace = /[ \r\n]+/
As = 'as'
If = 'if'
Else = 'else'
While = 'while'
Loop = 'loop'
Distinct = 'distinct'
Mut = 'mut'
Extern = 'extern'
Struct = 'struct'
Import = 'import'
Ident = /[A-Za-z_][A-Za-z0-9_]*/
Float = /[0-9]*\.[0-9]+([eE][-+]?[0-9]+)?/
Int = /[0-9]+/
Bool = /true|false/
_Quote
_Escape
_StringContents
Plus = '+'
Hyphen = '-'
Asterisk = '*'
Slash = '/'
Percent = '%'
Less = '<'
LessEquals = '<='
Greater = '>'
GreaterEquals = '>='
Bang = '!'
BangEquals = '!='
DoubleAnd = '&&'
DoublePipe = '||'
DoubleEquals = '=='
Equals = '='
Comma = ','
Dot = '.'
Arrow = '->'
Caret = '^'
LParen = '('
RParen = ')'
LBrack = '['
RBrack = ']'
LBrace = '{'
RBrace = '}'
_CommentLeader
_CommentContents
Colon = ':'
Semicolon = ';'
Error = !
__InternalString = /"([^"\\\n]|\\.)*"?"/
__InternalComment = ///.*/