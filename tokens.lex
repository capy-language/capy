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
Ident = /[A-Za-z_][A-Za-z0-9_]*/
Float = /[0-9]*\.[0-9]+([eE][-+]?[0-9]+)?/
Int = /[0-9]+/
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
// The string/char doesn't have to end on a quote, this results in better error messages
// this will internally get replaced by _SingleQuote, _Escape, and _StringContents
__InternalString = /"([^"\\\n]|\\.)*"?/
// this will internally get replaced by _DoubleQuote, _Escape, and _StringContents
__InternalChar = /'([^'\\\n]|\\.)*'?/
// this will internally get replaced by _CommentLeader and _CommentContents
__InternalComment = ///.*/
