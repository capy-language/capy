// This is a DSL I quickly put together to make it easier to
// make new tokens or alter existing tokens
Whitespace = /[ \t\r\n]+/
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
Comptime = 'comptime'
Return = 'return'
Break = 'break'
Continue = 'continue'
Ident = /[A-Za-z_][A-Za-z0-9_]*/
// these basically match numbers that can contain `_`,
// but must contain a digit as the first char
Float = /(\d[\d_]*)?\.(\d[\d_]*)+([eE][-+]?(\d[\d_]*)+)?/
Int = /(\d[\d_]*)+([eE](\d[\d_]*)+)?/
Bool = /true|false/
_SingleQuote
_DoubleQuote
_Escape
_StringContents
Plus = '+'
Hyphen = '-'
Asterisk = '*'
Slash = '/'
Percent = '%'
Left = '<'
DoubleLeft = '<<'
LeftEquals = '<='
Right = '>'
DoubleRight = '>>'
RightEquals = '>='
Bang = '!'
BangEquals = '!='
And = '&'
DoubleAnd = '&&'
Pipe = '|'
DoublePipe = '||'
Equals = '='
DoubleEquals = '=='
Tilde = '~'
Comma = ','
Dot = '.'
Arrow = '->'
Caret = '^'
Backtick = '`'
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
// The string/char doesn't have to end on a quote, this results in better error messages
// this will internally get replaced by _SingleQuote, _Escape, and _StringContents
__InternalString = /"([^"\\\n]|\\.)*"?/
// this will internally get replaced by _DoubleQuote, _Escape, and _StringContents
__InternalChar = /'([^'\\\n]|\\.)*'?/
// this will internally get replaced by _CommentLeader and _CommentContents
__InternalComment = ///.*/
