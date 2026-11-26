"""Holdout lists the viewer can browse.

Every list lives in one folder outside the repo:

    C:/Users/Rowan/Documents/BBHoldouts

Small lists are read once into memory with a line-offset index.  The
multi-hundred-MB lists have fixed-width lines, so a machine is found by
arithmetic instead: seek to (id-1)*stride and read one line.  Nothing of those
files is loaded until a machine from them is actually opened.

Machines are addressed by 1-based line number ("database id").
"""
import os
from pathlib import Path

LIST_DIR = Path(os.environ.get('BBHOLDOUTS_DIR', 'C:/Users/Rowan/Documents/BBHoldouts'))


class HoldoutList:
    def __init__(self, key, label, name, filename, url=None, fixed=False):
        self.key = key
        self.label = label              # BB(2,5)
        self.name = name                # short description
        self.url = url
        self.path = LIST_DIR / filename
        self.fixed = fixed
        self.has_id = False
        if fixed:                       # fixed-width lines, addressed by arithmetic
            size = self.path.stat().st_size
            digits = ''.join(c for c in self.path.stem.split('_')[-1] if c.isdigit())
            self.count = int(digits)
            self.stride = size // self.count
            if self.stride * self.count != size:
                raise ValueError('%s: %d bytes is not %d whole lines'
                                 % (filename, size, self.count))
            states, symbols = self.path.stem.split('_')[0].split('x')
            self.n, self.m = int(states), int(symbols)
        else:
            data = self.path.read_bytes()
            offs, start = [], 0
            while start < len(data):
                nl = data.find(b'\n', start)
                if nl < 0:
                    nl = len(data)
                if data[start:nl].strip():
                    offs.append(start)
                start = nl + 1
            self._data, self._offsets = data, offs
            self.count = len(offs)
            first = self._raw(1)
            token = first.split(None, 1)
            self.has_id = len(token) == 2 and token[0].isdigit()
            blocks = self.spec(1).split('_')
            self.n, self.m = len(blocks), len(blocks[0]) // 3
        self.domain = 'BB(%d,%d)' % (self.n, self.m)

    def _raw(self, i):
        """Line i as stored, id column included."""
        if self.fixed:
            with open(self.path, 'rb') as f:
                f.seek((i - 1) * self.stride)
                return f.read(self.stride).decode('utf-8', 'replace').strip()
        start = self._offsets[i - 1]
        end = self._data.find(b'\n', start)
        return self._data[start:end if end >= 0 else len(self._data)].decode(
            'utf-8', 'replace').strip()

    def spec(self, i):
        """1-based line number -> standard-format string."""
        if not 1 <= i <= self.count:
            raise IndexError(i)
        text = self._raw(i)
        if self.has_id:
            text = text.split(None, 1)[1].strip()
        return text

    def meta(self):
        return {'key': self.key, 'label': self.label, 'name': self.name,
                'count': self.count, 'url': self.url, 'domain': self.domain,
                'fixed': self.fixed}


LISTS = {L.key: L for L in (
    HoldoutList('bb25', 'BB(2,5)', '37 Rocq holdouts',
                'BB2x5_Rocq_holdouts_37.txt',
                'https://wiki.bbchallenge.org/w/images/c/c/BB2x5_Rocq_holdouts_37.txt'),
    HoldoutList('bb25b', 'BB(2,5)', '60 Rocq holdouts',
                'BB2x5_Rocq_holdouts_60.txt',
                'https://wiki.bbchallenge.org/w/images/BB2x5_Rocq_holdouts_60.txt'),
    HoldoutList('bb33', 'BB(3,3)', '6 holdouts',
                '3x3_holdout_6.txt',
                'https://wiki.bbchallenge.org/w/images/7/71/3x3_holdout_6.txt'),
    HoldoutList('bb6', 'BB(6)', '608 holdouts',
                'BB6_holdouts_608.txt',
                'https://wiki.bbchallenge.org/w/images/5/5e/BB6_holdouts_608.txt'),
    HoldoutList('bb26', 'BB(2,6)', '412,086 holdouts', '2x6_holdouts_412086.txt'),
    HoldoutList('bb43', 'BB(4,3)', '4,720,332 holdouts', '4x3_holdouts_4720332.txt',
                fixed=True),
    HoldoutList('bb34', 'BB(3,4)', '11,362,197 holdouts', '3x4_holdouts_11362197.txt',
                fixed=True),
    HoldoutList('bb72', 'BB(7,2)', '15,743,264 holdouts', '7x2_holdouts_15743264.txt',
                fixed=True),
)}

ORDER = ['bb25', 'bb25b', 'bb33', 'bb6', 'bb26', 'bb43', 'bb34', 'bb72']
DEFAULT = 'bb25'


def get(key):
    return LISTS.get(key) or LISTS[DEFAULT]
