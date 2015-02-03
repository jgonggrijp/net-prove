from pygments.style import Style
from pygments.token import Keyword, Name, Comment, String, Error, Number, Operator, Generic

class NetProveTermStyle(Style):
    default_style =             ''
    styles = {
        Comment:                'italic #888',
        Keyword.Reserved:       'bold',
        Keyword.Type:           '#80a',
        Operator:               'bold',
        String:                 '#f40',
        String.Escape:          '#0cf',
        Number:                 '#0b2',
    }