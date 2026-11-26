"""Viewer for busy-beaver holdout lists.

    python server.py [port]

  /                    player (one machine at a time, any list)
  /all?list=<key>      list view: std strings + pre-rendered diagrams (small lists)
  /api/lists           the available lists
  /api/new?list=&id=N  open machine N of a list (?spec=... ?morphett=...)
  ?tape=bi|semi        infinite both ways, or cells 0.. with a wall at the left
  ?init=1*01           starting tape, * marks the head (first cell to its right)
  /api/advance|reset|info|wiki|domain
  /d/<sid>.png         live 512x768 picture (?head=1, ?mode=blaze)
  /p/<key>/<n>.png     cached picture of machine n of list <key> (?steps=N)

Ids are 1-based line numbers in the list file.
"""
import http.server
import json
import pathlib
import random
import sys
import threading
import urllib.parse
import urllib.request

from lists import DEFAULT, LISTS, ORDER, get
from render import diagram
from sim import Session, draw, encode

HERE = pathlib.Path(__file__).resolve().parent
CACHE = HERE / 'cache'
STEPS = 1_000_000
MAX_ADVANCE = 50_000_000
WIKI_API = 'https://wiki.bbchallenge.org/w/api.php'

SESS = {}
IMG = {}
WIKI = {}
DOMAIN = {}
LOCK = threading.Lock()


def new_session(mid, spec, listkey, tape='bi', morphett=None, init=None):
    sid = '%08x' % random.getrandbits(32)
    with LOCK:
        SESS[sid] = Session(mid, spec, tape=tape, morphett=morphett, init=init)
        while len(SESS) > 12:                 # old machines are only reopened
            SESS.pop(next(iter(SESS)))        # through the list, so evict them
        info = SESS[sid].info()
    info['sid'] = sid
    info['list'] = listkey
    return info


def wiki(spec):
    """Does the machine have a bbchallenge wiki page, i.e. /wiki/<std string>?"""
    with LOCK:
        if spec in WIKI:
            return WIKI[spec]
    url = (WIKI_API + '?action=query&format=json&redirects=1&prop=info&inprop=url'
           '&titles=' + urllib.parse.quote(spec))
    out = {'exists': False, 'title': spec, 'url': None,
           'create': ('https://wiki.bbchallenge.org/w/index.php?title='
                      + urllib.parse.quote(spec.replace(' ', '_'))
                      + '&action=edit')}
    try:
        d = json.load(urllib.request.urlopen(url, timeout=15))
        for page in d.get('query', {}).get('pages', {}).values():
            if 'missing' in page or 'invalid' in page:
                break
            title = page.get('title', spec)
            out.update(exists=True, title=title, url=page.get('fullurl') or
                       ('https://wiki.bbchallenge.org/wiki/'
                        + urllib.parse.quote(title.replace(' ', '_'))))
    except Exception as e:                    # offline / wiki down: "create" link only
        out['error'] = str(e)
    with LOCK:
        WIKI[spec] = out
    return out


def domain(n, m):
    """The wiki page for the domain, i.e. /wiki/BB(n,m)."""
    key = (n, m)
    with LOCK:
        if key in DOMAIN:
            return DOMAIN[key]
    title = 'BB(%d,%d)' % (n, m)
    out = {'label': title, 'exists': False, 'url': None, 'title': title}
    try:
        d = json.load(urllib.request.urlopen(
            WIKI_API + '?action=query&format=json&redirects=1&prop=info&inprop=url'
            '&titles=' + urllib.parse.quote(title), timeout=15))
        for page in d.get('query', {}).get('pages', {}).values():
            if 'missing' in page or 'invalid' in page:
                break
            t = page.get('title', title)
            out.update(exists=True, title=t, url=page.get('fullurl') or
                       ('https://wiki.bbchallenge.org/wiki/'
                        + urllib.parse.quote(t.replace(' ', '_'))))
    except Exception as e:
        out['error'] = str(e)
    with LOCK:
        DOMAIN[key] = out
    return out


OVERVIEW = """<!doctype html>
<meta charset="utf-8">
<title>Holdouts &mdash; {label}</title>
<style>
  :root {{ color-scheme: dark; }}
  body {{ margin: 0; padding: 26px 24px 64px; background: #0b1119; color: #c9d1d9;
         font: 14px/1.55 -apple-system, "Segoe UI", system-ui, sans-serif; }}
  h1 {{ font-size: 19px; font-weight: 700; margin: 0 0 4px; color: #e6edf3; }}
  .sub {{ color: #7d8590; margin: 0 0 20px; font-size: 13px; }}
  .sub a {{ color: #58a6ff; text-decoration: none; }}
  ol {{ list-style: none; margin: 0; padding: 0; }}
  li {{ margin: 0 0 24px; }}
  .head {{ display: flex; gap: 12px; align-items: baseline; flex-wrap: wrap; }}
  .id {{ font-variant-numeric: tabular-nums; color: #6e7681; font-size: 13px;
         min-width: 3.6em; }}
  code {{ font: 13px/1.4 ui-monospace, Menlo, Consolas, monospace; color: #c9d1d9;
          word-break: break-all; }}
  img {{ display: block; margin: 8px 0 0 3.6em; width: calc(100% - 3.6em);
         max-width: 512px; image-rendering: pixelated; background: #000; }}
  .note {{ margin: 18px 0 0; color: #7d8590; font-size: 13px; }}
</style>
<h1>{label} holdouts &mdash; {count:,} machines</h1>
<p class="sub">{name}. ids are line numbers in the list file
{source}. Open the <a href="/">player</a> to step one. {nav}</p>
{body}
"""


def overview(listkey, steps):
    L = get(listkey)
    if L.count <= 64:
        items = ''.join(
            '<li><div class="head"><span class="id">#{i}</span>'
            '<code>%s</code></div>'
            '<img src="/p/%s/%d.png?steps=%d" alt="diagram of %d">'
            '<div class="note">%s steps</div></li>'
            % (L.spec(i), L.key, i, steps, i, format(steps, ','))
            for i in range(1, L.count + 1))
        body = '<ol>%s</ol>' % items
    else:
        rows = ''.join('<li><div class="head"><span class="id">#%d</span>'
                       '<code>%s</code></div></li>' % (i, L.spec(i))
                       for i in range(1, 41))
        body = ('<ol>%s</ol><p class="note">Showing the first 40 of %s \u2014 '
                'use the player to open any id, or random.</p>'
                % (rows, format(L.count, ',')))
    nav = ' · '.join('<a href="/all?list=%s">%s</a>' % (k, get(k).label)
                     for k in ORDER if k != L.key)
    source = ('from <a href="%s">the wiki</a>' % L.url if L.url
              else 'a local file')
    return OVERVIEW.format(label=L.label, name=L.name, count=L.count,
                           source=source, nav=nav, body=body).encode()


def png(listkey, n, spec, steps):
    CACHE.mkdir(exist_ok=True)
    f = CACHE / ('%s_%02d_%d.png' % (listkey, n, steps))
    if f.exists():
        return f.read_bytes()
    im, info = diagram(spec, steps=steps)
    data = encode(im)
    f.write_bytes(data)
    sys.stderr.write('%s#%d: %s\n' % (listkey, n, info))
    return data


class Handler(http.server.BaseHTTPRequestHandler):
    def do_GET(self):
        u = urllib.parse.urlparse(self.path)
        q = urllib.parse.parse_qs(u.query)
        p = u.path
        try:
            if p in ('/', '/index.html'):
                return self._send((HERE / 'app.html').read_bytes(),
                                  'text/html; charset=utf-8')
            if p == '/all':
                return self._send(overview(q.get('list', [DEFAULT])[0],
                                           int(q.get('steps', [STEPS])[0])),
                                  'text/html; charset=utf-8')
            if p.startswith('/m/') and p.endswith('.txt'):
                return self._send((HERE / p[3:]).read_bytes(),
                                  'text/plain; charset=utf-8')
            if p == '/api/lists':
                return self._json([get(k).meta() for k in ORDER])
            if p == '/api/new':
                tape = q.get('tape', ['bi'])[0]
                init = q.get('init', [''])[0]
                if 'morphett' in q:
                    return self._json(new_session(0, None, 'morphett', tape,
                                                  morphett=q['morphett'][0],
                                                  init=init))
                if 'spec' in q:
                    return self._json(new_session(0, q['spec'][0].strip(), 'spec',
                                                  tape, init=init))
                L = get(q.get('list', [DEFAULT])[0])
                n = int(q.get('id', ['1'])[0])
                return self._json(new_session(n, L.spec(n), L.key, tape, init=init))
            if p == '/api/wiki':
                return self._json(wiki(q.get('spec', [''])[0].strip()))
            if p == '/api/domain':
                return self._json(domain(int(q.get('n', ['0'])[0]),
                                         int(q.get('m', ['0'])[0])))
            if p.startswith('/api/') and p[5:] in ('advance', 'reset', 'info'):
                return self._session(p[5:], q)
            if p.startswith('/d/') and p.endswith('.png'):
                return self._send(picture(p[3:-4], q), 'image/png')
            if p.startswith('/p/'):
                parts = p[3:].split('/')
                if len(parts) == 2 and parts[1].endswith('.png'):
                    L = get(parts[0])
                    n = int(parts[1][:-4])
                    steps = max(1, min(int(q.get('steps', [STEPS])[0]), 20_000_000))
                    return self._send(png(L.key, n, L.spec(n), steps), 'image/png')
        except ValueError as e:
            return self._send(b'bad request: %s' % str(e).encode(), 'text/plain', 400)
        except (KeyError, IndexError) as e:
            return self._send(b'bad request: %s' % str(e).encode(), 'text/plain', 404)
        self._send(b'not found', 'text/plain', 404)

    def _session(self, what, q):
        sid = q.get('sid', [''])[0]
        with LOCK:
            s = SESS.get(sid)
            if s is None:
                raise KeyError(sid)
            if what == 'advance':
                n = max(0, min(int(q.get('n', ['1'])[0]), MAX_ADVANCE))
                info = s.advance(n)
            elif what == 'reset':
                s.reset()
                info = s.info()
            else:
                info = s.info()
        info['sid'] = sid
        return self._json(info)

    def _json(self, obj):
        return self._send(json.dumps(obj).encode(), 'application/json')

    def _send(self, body, ctype, code=200):
        self.send_response(code)
        self.send_header('Content-Type', ctype)
        self.send_header('Content-Length', str(len(body)))
        self.send_header('Cache-Control', 'no-store')
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, fmt, *args):
        sys.stderr.write('%s %s\n' % (self.address_string(), fmt % args))


def picture(sid, q):
    """Render a session diagram, outside the session lock."""
    head = q.get('head', ['0'])[0] == '1'
    mode = q.get('mode', ['default'])[0]
    if mode not in ('default', 'explore', 'blaze'):
        mode = 'default'
    with LOCK:
        s = SESS.get(sid)
        if s is None:
            raise KeyError(sid)
        snap = s.snapshot()
    key = (sid, snap['step'], head, mode)
    with LOCK:
        if key in IMG:
            return IMG[key]
    data = encode(draw(snap, mode=mode, head=head))
    with LOCK:
        if len(IMG) > 64:
            IMG.clear()
        IMG[key] = data
    return data


if __name__ == '__main__':
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8777
    srv = http.server.ThreadingHTTPServer(('127.0.0.1', port), Handler)
    print('http://127.0.0.1:%d/' % port, flush=True)
    srv.serve_forever()
