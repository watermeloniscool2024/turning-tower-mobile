#!/usr/bin/env python3
"""
==========================================================================
  T H E   T U R N I N G   T O W E R   v2
  GMI Game Jam 2026  -  secret theme: UP AND DOWN ROUND AND ROUND
==========================================================================

A pixel-art dark-tower platformer.  THIS IS THE KIVY MOBILE (touch, native keyboard) BUILD: same game
logic, rendered with Kivy.  Every sprite is drawn from pixel data in this file and
every sound / song is synthesised on the fly - there are no asset files.

  UP AND DOWN, LEFT AND RIGHT
      Gravity is not a button.  It lives IN the tower: gravity crystals,
      wind fields, updrafts.  Touch a crystal and the world's "down" turns
      to up, left or right.  Walk on ceilings and walls.  Press the key that
      points AWAY from the surface you're standing on to jump.

  ROUND AND ROUND
      The tower is a ring.  Walk, fall or ride the wind off one edge and
      you come out of the other.  Each floor's exit is further round than
      its entrance, so you spiral.  The background turns as you climb.

  Modes:  CAMPAIGN (18 floors, 6 worlds, some upside-down)
          ENDLESS TOWER (procedural, lives, score, high-score)
          DAILY TOWER (same tower for everyone today, best-time board)

Run:      python the_turning_tower.py
Options:  --windowed     run in a window instead of fullscreen
          --mute         start with audio off

Controls
  A D / arrows     move along your surface   (on a wall: W S / up down)
  SPACE / Z / K    jump        or press the key pointing AWAY from your surface
  R                respawn at checkpoint      ESC / P    pause
  F11              fullscreen                 M          mute

Audio: Windows (winmm), macOS (afplay), Linux (paplay/aplay).  If nothing
works the game just runs silent.
"""

import array
import hashlib
import json
import math
import os
import random
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import wave
TT_MOBILE = True
# ---- Kivy port: imports / config (must run before kivy.core.window is imported) ----
os.environ.setdefault('KIVY_NO_ARGS', '1')
os.environ.setdefault('KIVY_NO_CONSOLELOG', '0')
from types import SimpleNamespace
from kivy.config import Config
from kivy.utils import platform as kplatform
Config.set('kivy', 'exit_on_escape', '0')
Config.set('kivy', 'log_level', 'warning')
if kplatform in ('win', 'linux', 'macosx'):
    Config.set('input', 'mouse', 'mouse,disable_multitouch')
    Config.set('graphics', 'width', '1280')
    Config.set('graphics', 'height', '720')
    Config.set('graphics', 'resizable', '1')
    Config.set('graphics', 'fullscreen', '0' if '--windowed' in sys.argv else 'auto')
else:
    Config.set('graphics', 'fullscreen', 'auto')
    Config.set('graphics', 'resizable', '0')
from kivy.app import App
from kivy.clock import Clock
from kivy.core.window import Window
from kivy.graphics import Color, Rectangle, Mesh
from kivy.graphics.texture import Texture
from kivy.uix.widget import Widget
try:                                    # HTTPS on Android needs a CA bundle
    import certifi
    os.environ.setdefault('SSL_CERT_FILE', certifi.where())
except Exception:
    pass
tk = None   # tkinter is gone in this port

# ============================================================================
#  CONSTANTS
# ============================================================================
TILE = 16
RW = 28                       # ring width in tiles (fixed for every tower)
HWID = 4                      # width of the holes between floors
SLAB = 2                      # thickness of a floor slab
PS = 11                       # player hitbox (square)
DT = 1.0 / 60.0

GRAV = 0.32
MAXV = 6.4
FIELD_MAXV = 3.4
JUMP = 5.6
SPRING_V = 7.6
RUN = 1.9
ACC_G, ACC_A = 0.34, 0.20
FRC_G, FRC_A = 0.40, 0.06
COYOTE, BUFFER = 6, 6
CRYSTAL_CD, SPRING_CD = 8, 10
CRUMBLE_T, CRUMBLE_RET = 42, 260

DOWN, UP, LEFT, RIGHT = 0, 1, 2, 3
GVEC = ((0, 1), (0, -1), (-1, 0), (1, 0))
OPP = (1, 0, 3, 2)
MIRD = (0, 1, 3, 2)
DNAME = ('down', 'up', 'left', 'right')
DIRCOL = {0: '#ffb04a', 1: '#5ff0fb', 2: '#7dffb0', 3: '#ff6ad5'}

C_BG = '#0a0813'
C_PANEL = '#0d0a1c'
C_EDGE = '#4d4399'
C_TEXT = '#e6e0ff'
C_DIM = '#7a72b0'
C_FAINT = '#4a4380'
C_GOLD = '#f0c75e'
C_CYAN = '#8ff7ff'
C_RED = '#e0245e'
C_PURPLE = '#a56bff'
C_SHUTTER = '#05040a'

K_LEFTK = {'left', 'a'}
K_RIGHTK = {'right', 'd'}
K_UPK = {'up', 'w'}
K_DOWNK = {'down', 's'}
K_JUMPK = {'space', 'z', 'k'}
K_OK = {'return', 'space', 'z', 'kp_enter'}
K_BACK = {'escape', 'backspace'}

try:
    _HERE = os.path.dirname(os.path.abspath(__file__))
except NameError:
    _HERE = '.'
if getattr(sys, 'frozen', False):
    # packaged .exe: keep saves and the audio cache in a real folder (a onefile
    # build unpacks to a temp dir that is deleted on exit)
    _HERE = os.path.join(os.environ.get('APPDATA') or os.path.expanduser('~'), 'TheTurningTower')
    try:
        os.makedirs(_HERE, exist_ok=True)
    except Exception:
        pass
if kplatform == 'android':
    _HERE = os.path.join(os.environ.get('ANDROID_PRIVATE') or _HERE, 'tt')
elif kplatform == 'ios':
    _HERE = os.path.join(os.path.expanduser('~/Documents'), 'TheTurningTower')
else:
    try:
        _t = os.path.join(_HERE, '.wtest')
        open(_t, 'w').close()
        os.remove(_t)
    except Exception:
        _HERE = os.path.join(os.path.expanduser('~'), '.theturningtower')
try:
    os.makedirs(_HERE, exist_ok=True)
except Exception:
    pass
SAVE_PATH = os.path.join(_HERE, 'turning_tower_save.json')
CACHE_DIR = os.path.join(_HERE, 'tt_audio_cache')

# The hooded wanderer: window / taskbar icon, embedded as base64 PNG (no file needed).
ICON_B64 = (
    'iVBORw0KGgoAAAANSUhEUgAAAEAAAABACAYAAACqaXHeAAAOh0lEQVR42tWbXYhd13XHf2vtfc69M9LMSLJcxx9tHOomlj8KCSEl'
    'Ly7EJm7akNK00MdQQ+lDEwikpAkEWhpoSgl9McUPJQ/9oGBoCv0waaEllDRNCw1xncrBwaSWbSJjoUq25uPOPWev1Ye9z7nnztzR'
    'SDOjjHrFoJHuPefuvfZa//Vf/7WOcAtfJ0c/5SoVeAtigOE+AnFQgTT/eREBb3F3RAKo4DRc23pZbtUa4600gLvjYiAgKrhFVCRv'
    'zB1Edn0ejSCOY6g5ht/KJR69AcZx7UOxXvntdjK6+ksf/U3cBfUap+Xuu+4nxjHSeYAVQwAuhplx8Y0LpJTK4gypWv70r37vP+48'
    'ffbqpSsvP3nbG0DDyV+VtPbhOp7EttcAaN0RqYl2Bt8Ovef7MAZcAbDNS4gYAAnD2obV8T0f2N7S/y8hoGdFHDcvsZzd3MzK7wLl'
    '1IUwAIBZGHSRIdJ5iOKebokBjsysa8sP+sn6QQ+c+jhe94vvXHznv2e7ln73ZoYHx8RwdRIpG80EUFbHD/nq+BF/6qlPvv+2M4C4'
    'ZuTGQFrEKkIEdwEM1Yir47IXoAshhN4rssdUhCAI9dxym82j84BDp5fVpXPuBh994lOILmGW47fSMfe844HefUPQHtwWf30XMjpI'
    'izkk/ufV5wlxjGp+7+KlF/j2f30NDc7Vje/JsWJATmegGrES8+5O0zQ4LUIESaQEiCGEATbI7B5QNu8DkxjuQlWNcEk4qYQRPTYc'
    'Pwj6YBPms3MVyciuCaxszLVwIAXPoT3DBOmN4G4lDFrcYk6bHrPhMKQYqUnT4zeADGJ6htp5Q0KNWwMyc32T6weh52AAIPgYo4Gk'
    'uHTeNfO8EMPxG2CI6sO016Sr/MlffBpP9ZyhRNmRCWYb32kPVcXM+PkPfwJSuq7xjzEEDNGAeAKpekNUdWBqlxGV+aTj5Ewxl4Rs'
    'j8wiiI8gtYgZJmXToogI1qbbJwREBNLMTds0RbQFr0C3D3j3gARH6glihrctoa7yfVGc2wADus3nk5mRnVhFVtZiBkKpdxGiOcMV'
    'wNvt1hH3xPnvf4MYAlbufW39Cu5OPaqdyTETIeuATxrcU8n5goctRBxZ8A2qmt+LDVMMfEQyZbM10FCWpYBRpQZnxNttBrxGE5s6'
    'IYwjKW0f/vCOgggJkZWVCpPpfHoU38Xh+5N35a045lf+5l9AKj72YIW78Yl3P8JqqRIjznpd88tf/SZOzeOP1IyT8e1nn+PpT32O'
    'Nmz65sYrerwYQMRpcW17TpDfsEKDF2cNk0TtW7Q+piGRaPGYc71ZDpHNIIxMSGHEpkPjUOOYChbk9sgCTgse+gw+S4faU9mFsedG'
    'hfOLjyhbpvz1965SJSHUa8jkbcBYmSamMfDkwxVbCb51/k2mLHHptTexpmUp1mwcezHkIcez5L/BkOL6sxOywQ/58wSUJUIDJxxG'
    'Emh8GXPKfcB1Od+/hbUAbb3MNI7YYJkYQKhugywgKas+LNG0ccDSHDdBAPem5+65Ysy0eLo+YXU7h8sDk02SwD9aAB+BO6kVTJyV'
    'Fk608K7JFutpm21JJKkwn94GIDh+yA3nvQ//LJFxX82Zb3F5/XXMhYDjpkXr24fFDUJGiLgklsZncE8oARCuvP1DLr5xAcKmX9u8'
    'oMcbAiiikJqY1+4KrrnQMUE8ixmI75JApNuwz7CjL64MVGqCVGBZV3AEUSXocuYbdkyS2G/82mceevbZfz5vNs0xT+T+n3gY96Xe'
    'plEmBFsGEy5vvEzWwHWOOO2sI+Zdc4lTp34cT3DvnefAMs6oKq/Wz/Paxe9QhVOytrTqzpS3t16SH5kBttJ05Ex7HV8soBppU6IT'
    '+xOOq2C0JE+IZk2ww4VOOOlDoTOApEJzt6CdgCtFB8ElYSSmaZ2akzRpKxsmxB8NBpxcfsdUfS0+9MBj/OT9PyOppfByQxjPixs6'
    '5YXz/5pBrxCkM6fPZlce0OKdr/+98mafYMUUPPLeR5/o1SQTePTcd/jIz/0AJfKu938AlTH33fVlkqxybfJ9uWUeIIwiqKjWWAoI'
    'mlHeqtwAwfpNJdsmE/WAeCzEKKAuvS447/aKYriVtKotqoqbkFKD7eDUMnkr44GsE30CMjoQpN2QAZ555s8/aY3x2d/6IkGlAJUh'
    'EnAiqBcBJPQb01DhoiCwFE8g2jJqrxDTNNP9gQqgDkkCai2T0ZjWc6xvT7dwyuZ1ZrTVlRVOnz3NxIX11y4QdIzpNmIr/OEffOVz'
    '4xGTjY2rr33+C5/56pEY4LOf/v2nIRJ0ee6Uc2Njd3tLRDAXhCyFLY+XsFCzNHmBsU/wtmj9PSh6VoExTiyfI8kJwNmebiEiWRhh'
    '1meIy2PuOvceQuO89M1/w71CkuECX/ydP/pSxov1TeBoDCBSZTCSXKmpdrq/QX/qQv4Dlowwqvp05u4kNWJcx9O1UjqnQpJKGIQq'
    '9wPVSO4gLWYtIVRZcE0p46sIKdWk5m6UyCRcRL1G/AJOzOlVneTjw4Pg6vgRB/jYE5+nHZSe7g2j0RJta2UDxn33vIcqjvKZu5P8'
    'Kn//T1/B3Dlz+l6WRjVf/sIGQV5AtOW+d56dA8PRPT+NuPMLT75Iat+Je+LK1UsYNR95/NeJUvcetjF5iyvXfkjbJjyNEWlorCFK'
    '7O+n9QZ/+7VnUIW3ts7LgTygc7mU0lzuFqlp2xZ3IRRKE0VzJbdII/SK7e2UPcYUJ/Mi92rQE8gw2BlFVUl0JEnnMoanKe3UEEaI'
    'TgBlLEaSReGohwgBdQRQ99zVccM75PdskFSKHhOQ0g7Pbe68GBXJ3CA0iAfMIIQRZgI0vSOqQ9K2E8exYnCzrny2PtRMa8BKJZqr'
    '0CTVXMGFFSMWpelQVDhbX0vFN6vDh2ls5//loqdrnGR939xRhWRb2VAWst6PZq1fQrne+4106pGZ9eQp6Cz0dnrHTE3yPUvxG/aA'
    '7L67Nf+5G2tuUxQBaNYELc0R79Kdt3zpd/8dmSRcHbiAlmYHwFRfz2ry8gfZ7lKpFzOo7BKO+02X70ekKzeK0YsBJRwiBGz3FIfk'
    'hDRnIPd8hiZd50PQzlPcCW4kCUy27qKWDazNqXQoltUNGMp6s41r7F2z6ziZ5HviNhiq2NFd7NtlMvMmOUwalEJwRLD+i31vwPSc'
    'BvPnizpcUiMemcY7mcqZWZgMPEZCdmd0tLBA0iEIXodK7/QSs3R4HpBd2ueGF3ZpfGY9D3B3SAYlFMyFIC2T6hSY7Vq4CySZbVSS'
    'gra7QhBzxLzggvTZZGd3aVF1eTAMyA6QFZ6i++ehBSf5JuKZpIgIozFM1qe4SK7eoqHuSFmslGapF1EkZ5BBf6DbqCmI0TYltCwg'
    'YYpt52wTYqQeOW3aJoSq3Mtxi738lr9PSzNVDgeC3rvaLD+/+vqLXL76Su7Xe17wd1/8Ou1AoqpCxR1n7i2NEitA6Hla7HouXNJo'
    'CJHTa/eANPzdP/xxzzg7Q5o3vScIkXPv/iAqSzOwdi9apRw8De6V5lQD2o+65XTmJIIoWmpESx3Pt36w4caamoMZIXVEYtmYleGp'
    'hKijUvVikpn19HxnQOzDg67vAdbzGcEk9Tgwk8ITZ0/dvbgYGvT3unGB3CiZnYpeh50PjX/HqTt2habl/jmXL1/KgxfiBJfMHhe2'
    '6w9FhBaf3F6k6EbnCbo+4o1eO7xmuLm9POrwREgHp1YoaVhQ/g4XJIumP/dY5I2ksWGtMPMQ7zNT761mKDnvz2mOfthy2OU66c93'
    't8gHrjUjLLLvwOuuSYG5a6Qfi8mldCe/lPAy6bNKnzbJOsJ+XnDDktiNxNOiLnBPi29y3mCXSnyDfcCdn9sJwAcohxefMDtPbJ8m'
    'x83E+H7l+SysCvEt7QQdAqgfQTGEByiDmiK5AA02sPScyxft4IDD3XZTJ9uBbyp1b0m9DJovkivS/UZs9XDLunnUPYhb7xeOHeiJ'
    'z+qLrlE7x5Vv1gD5lL1nZ0Pevwjxj9Ld90p/u7BCc+73NhGKMtV9PusHdjgeIKVXp27Efkgv4EwRkxKDflM9lusZTgc/e598xx+k'
    'H6BMvYhiaFZicxr3w+gBkru6ZoahfaMiBCXGeo9HXo4+VHYbwQZl+vYAEyIp5fc85e6y6GHToBjmGyTfxJMTtKJNm0WaGs2Fgt+k'
    'J+yH9vsCpxkxLCHitHaNZOulVlHqSgbGOigTpMZJnH/pG0iYbfJkvcrplbsWLFJKONC3v67HH3QB5M5u6YRS0g6VHUPyrHG5w+mT'
    'p0HhxZf+sxdNcjPFmauzD+YBXb8vS9aFlA42tPjEc4k64wLDJYSbIFT71Qm5XC/szwQJRYg1R6KBNPODWzdfDTYIypnTd5c2V3a7'
    'IDNOvmf57Pu3Xxah+l4b3Wvgyss06o+dubcfp1dVkmyVblU8DAgqYoq31oNJ55ZdejFxAopKJHkzw4PBgnfKVqlrfuzCXMcHj9DM'
    'U+P8o5Kv94LyaqH0CLw3FDgaBZWAeXvw1lj3OjV+1M2GKJx62dlRlMD7Hn2sl6V2UlbbEffGQGZb2FPYe75QRLi6/gY/eOV8fjRn'
    '0JGmZCozo/G3rm01r64eSXO0pZ2BU5nW7lOPB5yW5BkAFz0/MDc/uYdKt9cs8aIiyUi4tL1k11eP3pI8P6RZh2hbzSFF0e61Ptn7'
    'uZxTSw+5kVBs0NmZ31AclsZ4Rus9ZO79UmCPBeKEGPzK+n8f76ism5YeYlUECl+szckwv/vCTbnnuSIfDE7M8lHvgoQwAg80zeGH'
    'pQ9tgKTXnrZkJyxsPKWWBxxd8yCkzuX33CWSDhPE0PK0aGuGaMkzQ8+QoVek8iid0nLtz5z1qVY8zyFtcGRPZa8sPeB5vmc253dd'
    'NiezmcBZU0/2r/7Eeezx933ouef+8utHse4je3CyrvPTXapl1lcSGhwN+XdRQ0NOXfmBykSIZcjStvtrup/u2hAzH/FS2ron1taq'
    't49q3f8HtfuctFnFnwUAAAAASUVORK5CYII='
)


def wrapd(d, size):
    """Shortest signed distance on a ring of circumference `size`."""
    return (d + size / 2.0) % size - size / 2.0


def blend(a, b, t):
    ar, ag, ab = int(a[1:3], 16), int(a[3:5], 16), int(a[5:7], 16)
    br, bg, bb = int(b[1:3], 16), int(b[3:5], 16), int(b[5:7], 16)
    return '#%02x%02x%02x' % (int(ar + (br - ar) * t), int(ag + (bg - ag) * t),
                              int(ab + (bb - ab) * t))


# ============================================================================
#  WORLD THEMES
# ============================================================================
THEMES = [
    dict(name='THE FOYER', stones=('#27214a', '#2c2552', '#231d42', '#2a2350'), hi='#3a3166',
         mortar='#0f0c1d', lip1='#7d6fd6', lip2='#52479f',
         bg=('#0e0b1c', '#100d20', '#0c0a19', '#110e22'), bgm='#07050e', bgh='#13102a',
         ring=('#1a1634', '#2f2860'), glow=('#40231a', '#2c1914', '#1e1311'),
         sky=('#101a44', '#0b1236', '#080d28'), frame='#2d2756',
         flame=('#ffe27a', '#ff8a2a', '#d94a1e'),
         amb=('rise', ('#ff8a2a', '#d94a1e', '#ffd75a')), accent='#a56bff', mood='foyer'),
    dict(name='THE CATACOMBS', stones=('#1f3a38', '#244240', '#1b3331', '#22403c'), hi='#33595a',
         mortar='#08130f', lip1='#6fd6b8', lip2='#3f9a85',
         bg=('#0a1512', '#0c1815', '#08110f', '#0d1a16'), bgm='#050b09', bgh='#12241f',
         ring=('#12302b', '#1f5249'), glow=('#16342a', '#10261e', '#0c1c16'),
         sky=('#0f2a2e', '#0a1e22', '#07161a'), frame='#25504a',
         flame=('#d8ffb0', '#7dffb0', '#2fb07a'),
         amb=('rise', ('#7dffb0', '#2fb07a', '#d8ffb0')), accent='#7dffb0', mood='catacomb'),
    dict(name='THE FURNACE', stones=('#3d1e1b', '#46231f', '#341a17', '#40201c'), hi='#5e332c',
         mortar='#140807', lip1='#ff9a4a', lip2='#b0502a',
         bg=('#160a09', '#190c0a', '#120807', '#1b0d0b'), bgm='#0a0403', bgh='#2a1310',
         ring=('#2a120e', '#5a2a1c'), glow=('#52240f', '#391a0c', '#281208'),
         sky=('#3a0f0a', '#2a0a07', '#1d0705'), frame='#5a2c22',
         flame=('#fff2a0', '#ffb02a', '#e0501e'),
         amb=('rise', ('#ffb02a', '#e0501e', '#fff2a0')), accent='#ff9a4a', mood='furnace'),
    dict(name='THE FROST', stones=('#243a55', '#2a4260', '#1f3550', '#28405c'), hi='#3d5e85',
         mortar='#0a1220', lip1='#cfeeff', lip2='#7fb4e0',
         bg=('#0b1220', '#0d1526', '#09101c', '#0e182a'), bgm='#060a14', bgh='#16233c',
         ring=('#14223a', '#2a4670'), glow=('#18304a', '#122438', '#0d1a2a'),
         sky=('#122848', '#0c1d38', '#08142a'), frame='#35557f',
         flame=('#e8f8ff', '#8fd0ff', '#4a86e0'),
         amb=('fall', ('#ffffff', '#cfeeff', '#9fd0ff')), accent='#8fd0ff', mood='frost'),
    dict(name='THE VOID', stones=('#2b1840', '#321d4a', '#26143a', '#2f1a45'), hi='#48296a',
         mortar='#0c0614', lip1='#ff6ad5', lip2='#a8348f',
         bg=('#0d0716', '#100a1b', '#0a0512', '#120b1e'), bgm='#05030a', bgh='#1d1030',
         ring=('#241040', '#4a1f70'), glow=('#40154a', '#2d0f36', '#1f0a26'),
         sky=('#220a3a', '#18062c', '#0f041e'), frame='#4a2a70',
         flame=('#ffd0f4', '#ff6ad5', '#9a2ac0'),
         amb=('rise', ('#ff6ad5', '#a56bff', '#ffd0f4')), accent='#ff6ad5', mood='void'),
    dict(name='THE CLOCKWORK', stones=('#3a3020', '#43382a', '#322a1c', '#3d3324'), hi='#5a4c36',
         mortar='#120e08', lip1='#f0c75e', lip2='#a8873a',
         bg=('#14100a', '#17130c', '#110d08', '#19150e'), bgm='#0a0805', bgh='#262014',
         ring=('#2a2214', '#5c4a22'), glow=('#4a3a14', '#34280e', '#241a0a'),
         sky=('#2a2208', '#1e1806', '#140f04'), frame='#5a4a28',
         flame=('#fff2b0', '#f0c75e', '#b07a1a'),
         amb=('fall', ('#f0c75e', '#a8873a', '#fff2b0')), accent='#f0c75e', mood='clock'),
]

SKINS = [
    ('WANDERER', 0, dict(c='#4b3b86', d='#2b2152', h='#6e5bb8', b='#e0b04a')),
    ('EMBER', 6, dict(c='#8a2f2f', d='#4a1818', h='#c24a3a', b='#ffd75a')),
    ('MOSS', 12, dict(c='#2f7a4a', d='#17402a', h='#4fb06f', b='#d8ffb0')),
    ('FROST', 20, dict(c='#4a86b8', d='#24435f', h='#8fd0ff', b='#ffffff')),
    ('GOLDEN', 30, dict(c='#a88a2a', d='#5a4814', h='#f0c75e', b='#ffffff')),
    ('VOID', 45, dict(c='#2a1a40', d='#120a1f', h='#ff6ad5', b='#8ff7ff')),
]

# ============================================================================
#  PIXEL FONT  (3x5)
# ============================================================================
FONT = {
    'A': ("010", "101", "111", "101", "101"), 'B': ("110", "101", "110", "101", "110"),
    'C': ("011", "100", "100", "100", "011"), 'D': ("110", "101", "101", "101", "110"),
    'E': ("111", "100", "110", "100", "111"), 'F': ("111", "100", "110", "100", "100"),
    'G': ("011", "100", "101", "101", "011"), 'H': ("101", "101", "111", "101", "101"),
    'I': ("111", "010", "010", "010", "111"), 'J': ("001", "001", "001", "101", "010"),
    'K': ("101", "101", "110", "101", "101"), 'L': ("100", "100", "100", "100", "111"),
    'M': ("101", "111", "111", "101", "101"), 'N': ("110", "101", "101", "101", "101"),
    'O': ("010", "101", "101", "101", "010"), 'P': ("110", "101", "110", "100", "100"),
    'Q': ("010", "101", "101", "110", "011"), 'R': ("110", "101", "110", "101", "101"),
    'S': ("011", "100", "010", "001", "110"), 'T': ("111", "010", "010", "010", "010"),
    'U': ("101", "101", "101", "101", "111"), 'V': ("101", "101", "101", "101", "010"),
    'W': ("101", "101", "111", "111", "101"), 'X': ("101", "101", "010", "101", "101"),
    'Y': ("101", "101", "010", "010", "010"), 'Z': ("111", "001", "010", "100", "111"),
    '0': ("111", "101", "101", "101", "111"), '1': ("010", "110", "010", "010", "111"),
    '2': ("110", "001", "010", "100", "111"), '3': ("110", "001", "010", "001", "110"),
    '4': ("101", "101", "111", "001", "001"), '5': ("111", "100", "110", "001", "110"),
    '6': ("011", "100", "111", "101", "111"), '7': ("111", "001", "010", "010", "010"),
    '8': ("111", "101", "111", "101", "111"), '9': ("111", "101", "111", "001", "110"),
    '.': ("000", "000", "000", "000", "010"), ',': ("000", "000", "000", "010", "100"),
    ':': ("000", "010", "000", "010", "000"), '!': ("010", "010", "010", "000", "010"),
    '?': ("110", "001", "010", "000", "010"), '-': ("000", "000", "111", "000", "000"),
    '/': ("001", "001", "010", "100", "100"), '>': ("100", "010", "001", "010", "100"),
    '<': ("001", "010", "100", "010", "001"), "'": ("010", "010", "000", "000", "000"),
    '+': ("000", "010", "111", "010", "000"), '(': ("010", "100", "100", "100", "010"),
    ')': ("010", "001", "001", "001", "010"), '*': ("000", "101", "010", "101", "000"),
    '&': ("010", "101", "010", "101", "011"), '=': ("000", "111", "000", "111", "000"),
    '^': ("010", "101", "000", "000", "000"), '%': ("101", "001", "010", "100", "101"),
    '#': ("101", "111", "101", "111", "101"),
}


# ============================================================================
#  PIXEL GRID HELPERS  (grids of colour strings or None)
# ============================================================================
def blank(w, h):
    return [[None] * w for _ in range(h)]


def flip_v(g):
    return [row[:] for row in g[::-1]]


def rot_cw(g):
    h = len(g)
    w = len(g[0])
    return [[g[h - 1 - c][r] for c in range(h)] for r in range(w)]


def rot_n(g, n):
    for _ in range(n % 4):
        g = rot_cw(g)
    return g


def orient(g, d):
    """g is drawn for 'up'; return it for direction d (0 down,1 up,2 left,3 right)."""
    if d == UP:
        return g
    if d == DOWN:
        return flip_v(g)
    if d == RIGHT:
        return rot_cw(g)
    return rot_n(g, 3)


def from_ascii(rows, pal):
    w = max(len(r) for r in rows)
    return [[pal.get(ch) for ch in r.ljust(w, '.')] for r in rows]


# ---- stone ------------------------------------------------------------------
GLYPHS = (
    ("00100", "01110", "10101", "00100", "01010"),
    ("10001", "01010", "00100", "01010", "10001"),
    ("01110", "10001", "10101", "10001", "01110"),
)


def g_brick(th, var, top, bot, rune, frame):
    rnd = random.Random(var * 977 + 13)
    g = blank(16, 16)
    for y in range(16):
        r = y // 4
        for x in range(16):
            xo = (x + (0 if r % 2 == 0 else 4)) % 8
            if y % 4 == 3 or xo == 0:
                c = th['mortar']
            else:
                c = rnd.choice(th['stones'])
                if y % 4 == 0:
                    c = th['hi']
            g[y][x] = c
    if top:
        g[0] = [th['lip1']] * 16
        g[1] = [th['lip2']] * 16
    if bot:
        g[15] = [th['lip1']] * 16
        g[14] = [th['lip2']] * 16
    if rune:
        rc = (th['accent'], blend(th['accent'], '#000000', 0.45))[frame]
        gl = GLYPHS[var % 3]
        for yy in range(5):
            for xx in range(5):
                if gl[yy][xx] == '1':
                    g[5 + yy][5 + xx] = rc
    return g


def g_crumble(th, state):
    g = g_brick(th, 1, True, True, False, 0)
    for y in range(16):
        for x in range(16):
            if g[y][x] is not None and g[y][x] not in (th['lip1'], th['lip2']):
                g[y][x] = blend(g[y][x], '#8a7a60', 0.25)
    cr = th['mortar']
    pts = [(3, 3), (4, 4), (5, 5), (5, 6), (6, 7), (7, 8), (8, 9), (8, 10), (9, 11)]
    if state:
        pts += [(11, 2), (10, 3), (10, 4), (9, 5), (12, 8), (11, 9), (11, 10), (2, 9), (3, 10)]
    for (x, y) in pts:
        g[y][x] = cr
    return g


def g_spike(d):
    g = blank(16, 16)
    for s in range(4):
        x0 = s * 4
        for y in range(8, 16):
            xs = (1, 2) if y < 10 else (0, 1, 2, 3)
            for x in xs:
                if y == 8:
                    c = '#ffffff'
                elif y >= 14:
                    c = '#4a4380'
                elif x in (0, 1):
                    c = '#d4cdf2'
                else:
                    c = '#8c84bd'
                g[y][x0 + x] = c
    return orient(g, d)


ARROW5 = ("00100", "01110", "10101", "00100", "00100")


def g_arrow5(d, col):
    g = blank(5, 5)
    for y in range(5):
        for x in range(5):
            if ARROW5[y][x] == '1':
                g[y][x] = col
    return orient(g, d)


def g_crystal(d, f):
    col = DIRCOL[d]
    dark = blend(col, '#000000', 0.55)
    lite = blend(col, '#ffffff', 0.55)
    g = blank(16, 16)
    for y in range(16):
        for x in range(16):
            dd = abs(x - 7.5) + abs(y - 7.5)
            if dd <= 7.2:
                if dd > 5.6:
                    c = dark
                elif dd > 3.0:
                    c = col
                else:
                    c = lite if f else col
                g[y][x] = c
    a = g_arrow5(d, '#ffffff' if f else '#10101a')
    for y in range(5):
        for x in range(5):
            if a[y][x] is not None:
                g[5 + y][5 + x] = a[y][x]
    return g


def g_field(d, f, acc):
    col = blend(acc, '#000000', 0.3)
    col2 = blend(acc, '#ffffff', 0.2)
    bgc = blend(acc, '#000000', 0.84)
    g = blank(16, 16)
    for y in range(16):
        for x in range(16):
            s = 15 - y
            p = x - 7.5
            if abs(p) <= 6.5 and (s + int(abs(p)) + f * 2) % 8 == 0:
                g[y][x] = col2
            elif (x + y) % 4 == 0:
                g[y][x] = bgc
            elif (x in (0, 15)) and y % 4 == f % 4:
                g[y][x] = col
    return orient(g, d)


SPR_PAL = {'p': '#ff6ad5', 'P': '#ffc0ea', 'g': '#c9c3e8', 'b': '#4a4380', 'k': '#0a0814'}


def g_spring(d, ext):
    if not ext:
        rows = ["................"] * 8 + [
            "..pppppppppppp..", "..PPPPPPPPPPPP..", ".....gg..gg.....",
            "......gggg......", ".....gg..gg.....", "......gggg......",
            "..bbbbbbbbbbbb..", "..bbbbbbbbbbbb.."]
    else:
        rows = ["................"] * 4 + [
            "..pppppppppppp..", "..PPPPPPPPPPPP..", ".....gg..gg.....",
            "......gggg......", ".....gg..gg.....", "......gggg......",
            ".....gg..gg.....", "......gggg......", ".....gg..gg.....",
            "......gggg......", "..bbbbbbbbbbbb..", "..bbbbbbbbbbbb.."]
    return orient(from_ascii(rows, SPR_PAL), d)


ORB_PAL = {'t': '#1a8f9b', 'T': '#37e0ee', 'W': '#ffffff', 'd': '#127585'}
ORB_ROWS = ("..tttt..", ".tTTTTt.", "tTWWTTTt", "tTWTTTTt",
            "tTTTTTTt", "tTTTTTdt", ".tTTTdt.", "..tttt..")
WISP_ROWS = ("..rrrr..", ".rRRRRr.", "rRRWWRRr", "rRWWWWRr",
             "rRWWWWRr", "rRRWWRRr", ".rRRRRr.", "..rrrr..")
WISP_PAL = (
    {'r': '#7a1230', 'R': '#e0245e', 'W': '#ffd6e6'},
    {'r': '#a01a3c', 'R': '#ff4d85', 'W': '#ffffff'},
)


def g_saw(f):
    g = blank(12, 12)
    for y in range(12):
        for x in range(12):
            dx, dy = x - 5.5, y - 5.5
            r = math.hypot(dx, dy)
            if r > 6.0:
                continue
            a = math.atan2(dy, dx) + f * math.pi / 8.0
            if r > 4.4:
                tooth = math.cos(a * 4) > 0.2
                g[y][x] = '#e8e8f8' if tooth else '#6a6a8a'
            elif r < 1.6:
                g[y][x] = '#2a2a40'
            else:
                spoke = abs(math.sin(a * 2)) < 0.28
                g[y][x] = '#4a4a6a' if spoke else '#9a9ab8'
    return g


PL_BASE_PAL = {'k': '#0a0814', 'f': '#120e1f', 'e': '#8ff7ff'}
PL_HEAD = [
    "................", "......kkkk......", ".....kchhck.....", "....kchhhhck....",
    "....kcffffck....", "....kEEEEEEk....", "....kcddddck....", "...kccddddcck...",
    "..kcchdbbdhcck..", "..kcchddddhcck..", "..kcddddddddck..",
]
PL_LEGS = {
    'stand': ["..kcddddddddck..", "..kcddddddddck..", "..kddddddddddk..",
              "...kkddddddkk...", "....kk....kk...."],
    'runA': ["..kcddddddddck..", "..kcddddddddck..", "...kdddddddddk..",
             "...kkddddddkk...", "...kk......kk..."],
    'runB': ["..kcddddddddck..", "..kcddddddddck..", "..kddddddddddk..",
             "....kddddddk....", ".....kkkkkk....."],
    'air': ["..kcddddddddck..", "..kcddddddddck..", "..kddddddddddk..",
            "...kddddddddk...", "....kkkkkkkk...."],
}


def g_player(frame, face, g, skin):
    rows = list(PL_HEAD)
    eyes = 'efefff' if face < 0 else 'fffefe'
    rows[5] = '....k' + eyes + 'k....'
    rows = rows + PL_LEGS[frame]
    pal = dict(PL_BASE_PAL)
    pal.update(SKINS[skin][2])
    base = from_ascii(rows, pal)
    if g == DOWN:
        return base
    if g == UP:
        return flip_v(base)
    if g == LEFT:
        return rot_cw(base)
    return rot_n(base, 3)


BRAZIER_PAL = {'k': '#0a0814', 's': '#3a3466', 'S': '#5a5090', 'o': '#6a2c1c',
               'y': '#ffe27a', 'O': '#ff8a2a', 'R': '#d94a1e'}
BRAZIER_BASE = [
    "................", "................", "................", "................",
    "................", "................", "................", "................",
    "...kkkkkkkkkk...", "...kssssssssk...", "...kSSssssssk...", "....kssssssk....",
    ".....kssssk.....", "......kssk......", "......kssk......", ".....kkkkkk.....",
]
FLAMES = [
    ["................", "................", ".......O........", "......OyO.......",
     "......OyyO......", ".....OyyyyO.....", ".....RyyyyR.....", "....RROyyORR...."],
    ["................", "........O.......", ".......OyO......", "......OyyO......",
     "......OyyyO.....", ".....OyyyyO.....", ".....RyyyyR.....", "....RROyyORR...."],
    ["................", "................", "......O.........", ".....OyO........",
     "......OyyO......", "......OyyyO.....", ".....RyyyyR.....", "....RROyyORR...."],
]


def g_brazier(th, lit, frame):
    rows = list(BRAZIER_BASE)
    pal = dict(BRAZIER_PAL)
    fl = th['flame']
    pal['y'], pal['O'], pal['R'] = fl[0], fl[1], fl[2]
    if lit:
        f = FLAMES[frame % 3]
        for i in range(8):
            rows[i] = f[i]
    else:
        rows[7] = "......o..o......"
    return from_ascii(rows, pal)


TORCH_PAL = {'k': '#0a0814', 's': '#4a4380', 'S': '#6a60a8'}
TORCH_BASE = [
    "........", "........", "........", "........", "........", "........",
    "........", ".kssssk.", "..kSSk..", "...kk...", "...ss...", "...ss...",
    "...ss...", "...ss...", "..kssk..", "..kkkk..",
]
TORCH_FLAME = [
    [(2, "...O...."), (3, "..OyO..."), (4, "..OyyO.."), (5, ".OyyyyO."), (6, ".RyyyyR.")],
    [(1, "....O..."), (2, "...OyO.."), (3, "..OyyO.."), (4, "..OyyyO."),
     (5, ".OyyyyO."), (6, ".RyyyyR.")],
]


def g_torch(th, frame):
    rows = list(TORCH_BASE)
    for (i, s) in TORCH_FLAME[frame % 2]:
        rows[i] = s
    pal = dict(TORCH_PAL)
    pal['y'], pal['O'], pal['R'] = th['flame']
    return from_ascii(rows, pal)


def g_chain():
    pal = {'g': '#3a3560', 'h': '#26224a'}
    rows = ["..gg..", ".g..g.", ".g..g.", "..gg..", "..hh..", "..hh.."]
    return from_ascii((rows * 3)[:16], pal)


def g_glow(th):
    size = 44
    g = blank(size, size)
    c = size / 2.0
    for y in range(size):
        for x in range(size):
            d = math.hypot(x + 0.5 - c, y + 0.5 - c)
            if d < 7:
                g[y][x] = th['glow'][0]
            elif d < 12:
                if (x + y) % 2 == 0:
                    g[y][x] = th['glow'][1]
            elif d < 18:
                if x % 2 == 0 and y % 2 == 0:
                    g[y][x] = th['glow'][2]
    return g


def g_bg_tile(th):
    rnd = random.Random(5)
    g = blank(64, 64)
    for y in range(64):
        r = y // 8
        for x in range(64):
            xo = (x + (0 if r % 2 == 0 else 16)) % 32
            if y % 8 == 7 or xo == 0:
                c = th['bgm']
            else:
                c = rnd.choice(th['bg'])
                if y % 8 == 0:
                    c = th['bgh']
            g[y][x] = c
    return g


def g_window(th):
    w, h = 24, 48
    rnd = random.Random(21)
    inside = [[False] * w for _ in range(h)]
    cx = (w - 1) / 2.0
    for y in range(h):
        for x in range(w):
            if y < 12:
                inside[y][x] = (x - cx) ** 2 + (y - 12) ** 2 <= 12.2 ** 2
            else:
                inside[y][x] = True
    g = blank(w, h)
    for y in range(h):
        for x in range(w):
            if not inside[y][x]:
                continue
            edge = False
            for dx, dy in ((-2, 0), (2, 0), (0, -2), (0, 2), (-1, 0), (1, 0), (0, -1), (0, 1)):
                xx, yy = x + dx, y + dy
                if not (0 <= xx < w and 0 <= yy < h) or not inside[yy][xx]:
                    edge = True
                    break
            if edge:
                g[y][x] = th['frame']
            else:
                t = y / float(h)
                base = th['sky'][0] if t < 0.35 else (th['sky'][1] if t < 0.7 else th['sky'][2])
                if rnd.random() < 0.025:
                    base = '#dfe9ff'
                g[y][x] = base
    for y in range(8, h - 2):
        g[y][11] = g[y][12] = th['frame']
    for x in range(2, w - 2):
        g[26][x] = g[27][x] = th['frame']
    return g


def g_door(th, frame):
    w, h = 16, 32
    g = blank(w, h)
    pur = (blend(th['accent'], '#000000', 0.6), blend(th['accent'], '#000000', 0.2), th['accent'])
    for y in range(h):
        for x in range(w):
            if y < 8:
                ok = (x - 7.5) ** 2 + (y - 8 + 0.5) ** 2 <= 8.2 ** 2
            else:
                ok = True
            if not ok:
                continue
            core = 2 <= x <= w - 3 and y >= 2 and (
                y >= 8 or (x - 7.5) ** 2 + (y - 8 + 0.5) ** 2 <= 5.9 ** 2)
            if core:
                dx = x - 7.5
                dy = y - 17.0
                r = math.hypot(dx, dy * 0.55)
                a = math.atan2(dy, dx)
                v = (r * 0.7 - frame * 1.3 + a * 1.2) % 3
                c = pur[int(v)]
                if r < 1.6:
                    c = '#ffffff'
                g[y][x] = c
            else:
                g[y][x] = th['lip2'] if (x in (0, w - 1) or y == 0) else th['frame']
    return g


STAR_ROWS = ["...a...", "...a...", "aaaaaaa", ".aaaaa.", "..aaa..", ".aa.aa.", ".a...a."]
HEART_ROWS = [".aa.aa.", "aaaaaaa", "aaaaaaa", ".aaaaa.", "..aaa..", "...a..."]


# ============================================================================
#  ASSETS  (turns pixel grids into zoomed PhotoImages, cached)
# ============================================================================
def _transparent(img, x, y):
    try:
        img.transparency_set(x, y, True)
    except Exception:
        try:
            img.tk.call(str(img), 'transparency', 'set', x, y, True)
        except Exception:
            pass


class Assets:
    def __init__(self, S):
        self.S = S
        self.cache = {}
        self.text_cache = {}
        self._old_text = {}

    def build(self, grid, zoom=None):
        z = zoom or self.S
        h = len(grid)
        w = len(grid[0])
        img = tk.PhotoImage(width=w, height=h)
        rows = []
        clear = []
        for y, row in enumerate(grid):
            cells = []
            for x, col in enumerate(row):
                if col is None:
                    cells.append('#000000')
                    clear.append((x, y))
                else:
                    cells.append(col)
            rows.append('{' + ' '.join(cells) + '}')
        img.put(' '.join(rows))
        for (x, y) in clear:
            _transparent(img, x, y)
        if z > 1:
            return img.zoom(z, z)
        return img

    def get(self, key, maker):
        im = self.cache.get(key)
        if im is None:
            im = self.build(maker())
            self.cache[key] = im
        return im

    # -- themed -------------------------------------------------------------
    def brick(self, th, var, top, bot, rune, frame):
        f = frame if rune else 0
        return self.get(('brick', th, var, top, bot, rune, f),
                        lambda: g_brick(THEMES[th], var, top, bot, rune, f))

    def crumble(self, th, state):
        return self.get(('crumble', th, state), lambda: g_crumble(THEMES[th], state))

    def brazier(self, th, lit, f, flip=False):
        ff = f if lit else 0

        def mk():
            g = g_brazier(THEMES[th], lit, ff)
            return flip_v(g) if flip else g
        return self.get(('braz', th, lit, ff, flip), mk)

    def torch(self, th, f):
        return self.get(('torch', th, f), lambda: g_torch(THEMES[th], f))

    def glow(self, th):
        return self.get(('glow', th), lambda: g_glow(THEMES[th]))

    def bg(self, th):
        return self.get(('bg', th), lambda: g_bg_tile(THEMES[th]))

    def window(self, th):
        return self.get(('window', th), lambda: g_window(THEMES[th]))

    def door(self, th, f, flip):
        def mk():
            g = g_door(THEMES[th], f)
            return flip_v(g) if flip else g
        return self.get(('door', th, f, flip), mk)

    def field(self, th, d, f):
        return self.get(('field', th, d, f), lambda: g_field(d, f, THEMES[th]['accent']))

    # -- shared -------------------------------------------------------------
    def spike(self, d):
        return self.get(('spike', d), lambda: g_spike(d))

    def crystal(self, d, f):
        return self.get(('crystal', d, f), lambda: g_crystal(d, f))

    def spring(self, d, ext):
        return self.get(('spring', d, ext), lambda: g_spring(d, ext))

    def saw(self, f):
        return self.get(('saw', f), lambda: g_saw(f))

    def arrow5(self, d, col):
        return self.get(('arrow5', d, col), lambda: g_arrow5(d, col))

    def orb(self, f):
        pal = ORB_PAL if f == 0 else {'t': '#1a8f9b', 'T': '#5ff0fb', 'W': '#ffffff', 'd': '#127585'}
        return self.get(('orb', f), lambda: from_ascii(ORB_ROWS, pal))

    def wisp(self, f):
        return self.get(('wisp', f), lambda: from_ascii(WISP_ROWS, WISP_PAL[f]))

    def player(self, frame, face, g, skin):
        return self.get(('pl', frame, face, g, skin), lambda: g_player(frame, face, g, skin))

    def chain(self):
        return self.get('chain', g_chain)

    def star(self, on):
        col = C_GOLD if on else '#2a2450'
        return self.get(('star', on), lambda: from_ascii(STAR_ROWS, {'a': col}))

    def heart(self, on):
        col = C_RED if on else '#2a2450'
        return self.get(('heart', on), lambda: from_ascii(HEART_ROWS, {'a': col}))

    def text(self, s, col, size):
        key = (s, col, size)
        im = self.text_cache.get(key)
        if im is None:
            if len(self.text_cache) > 4000:
                self._old_text = self.text_cache
                self.text_cache = {}
            n = len(s)
            g = blank(max(1, 4 * n - 1), 5)
            for i, ch in enumerate(s):
                rows = FONT.get(ch)
                if not rows:
                    continue
                for y in range(5):
                    for x in range(3):
                        if rows[y][x] == '1':
                            g[y][i * 4 + x] = col
            im = self.build(g, self.S * size)
            self.text_cache[key] = im
        return im


# ============================================================================
#  ROOMS   (each floor of the tower is one room; rooms are stacked & rotated)
# ============================================================================
MIRCH = {'<': '>', '>': '<', 'l': 'r', 'r': 'l', '3': '4', '4': '3'}


def cdist(a, b):
    d = abs(a - b) % RW
    return min(d, RW - d)


class Room:
    """
    A ring-shaped chamber, RW columns wide, H rows tall (row 0 = ceiling row).
    The player arrives through a HWID-wide hole in the floor (cols entry..)
    and leaves through an updraft field in the ceiling hole (cols exit..).

    Cell glyphs:  # brick   c crumble   u d l r  spikes pointing up/down/left/right
                  ^ v < >  gravity crystals     1 2 3 4  wind fields up/down/left/right
                  o soul   S spring   W orbiting wisps
    """

    def __init__(self, name, H, exit_col, fdepth=None):
        self.name = name
        self.H = H
        self.cells = [['.'] * RW for _ in range(H)]
        self.entry = 4
        self.exit = exit_col
        self.fdepth = H if fdepth is None else fdepth
        self.start = None
        self.door = None
        self.hint = None
        self.cp = 2
        self.diff = 1
        self.saws = []
        self.ents = []

    def put(self, c, r, ch):
        self.cells[r][c % RW] = ch

    def get(self, c, r):
        return self.cells[r][c % RW]

    def box(self, c0, r0, c1, r1, ch):
        for r in range(r0, r1 + 1):
            for c in range(c0, c1 + 1):
                self.put(c, r, ch)

    def mirrored(self):
        m = Room(self.name, self.H, None, self.fdepth)
        for r in range(self.H):
            for c in range(RW):
                ch = self.cells[r][c]
                m.cells[r][RW - 1 - c] = MIRCH.get(ch, ch)
        m.entry = (RW - HWID - self.entry) % RW
        m.exit = None if self.exit is None else (RW - HWID - self.exit) % RW
        m.start = None if self.start is None else RW - 1 - self.start
        m.door = None if self.door is None else RW - 1 - self.door
        if self.hint:
            m.hint = (self.hint[0], RW - 1 - self.hint[1], self.hint[2])
        m.cp = None if self.cp is None else RW - 1 - self.cp
        m.diff = self.diff
        m.saws = [dict(s, col=RW - 1 - s['col']) for s in self.saws]
        m.ents = [dict(e, c=RW - 1 - e['c']) for e in self.ents]
        return m


def r_start(rnd, spec):
    R = Room('START', 8, 18)
    R.diff = 0
    R.start = 12
    R.cp = None
    R.put(15, 6, 'o')
    R.put(16, 6, 'o')
    R.put(rnd.choice((22, 23)), 6, 'o')
    return R


def r_end(rnd, spec):
    R = Room('END', 8, None)
    R.diff = 0
    R.door = 16
    R.cp = None
    R.put(10, 6, 'o')
    R.put(22, 6, 'o')
    R.put(rnd.choice((12, 13, 19, 20)), 4, 'o')
    return R


def r_hall(rnd, spec):
    R = Room('HALL', 8, 16)
    R.diff = 1
    a = rnd.choice((10, 11))
    R.put(a, 7, 'u'), R.put(a + 1, 7, 'u')
    R.put(a, 4, 'o'), R.put(a + 1, 4, 'o')
    b = rnd.choice((22, 23))
    R.put(b, 7, 'u'), R.put(b + 1, 7, 'u')
    R.put(b, 4, 'o')
    if rnd.random() < 0.6:
        d = rnd.choice((13, 14))
        R.put(d, 0, 'd'), R.put(d + 1, 0, 'd')
    R.hint = ('JUMP OVER THE SPIKES', 9, 2)
    return R


def r_doors(rnd, spec):
    R = Room('DOORS', 9, 16)
    R.diff = 2
    for w in (rnd.choice((11, 12)), rnd.choice((23, 24))):
        t = rnd.choice((1, 2))
        R.box(w, 2, w + t - 1, 8, '#')
        for cc in (w - 3, w + t + 2):
            R.put(cc, 0, '^')
            R.put(cc, 8, '^')
    R.put(rnd.choice((14, 15)), 5, 'o')
    R.put(rnd.choice((25, 26)), 5, 'o')
    R.put(9, 3, 'o')
    R.hint = ('CRYSTALS TURN GRAVITY. TOUCH ONE.', 9, 4)
    return R


def r_ceilings(rnd, spec, wisps=False):
    R = Room('GUARDS' if wisps else 'CEILINGS', 8, 18)
    R.diff = 3 if wisps else 2
    for c in list(range(10, 18)) + list(range(22, 28)):
        R.put(c, 7, 'u')
    R.put(9, 7, '^'), R.put(3, 7, '^')
    R.cp = 1
    p1 = rnd.choice((13, 14))
    p2 = rnd.choice((24, 25))
    for p in (p1, p2):
        R.put(p, 0, 'd'), R.put(p + 1, 0, 'd')
    R.put(p1 + 2, 2, 'o')
    R.put(p2 + 2, 2, 'o')
    if wisps:
        R.put(15, 3, 'W')
        R.put(26, 3, 'W')
    R.hint = ('SPIKES BELOW? WALK THE CEILING.', 9, 3)
    return R


def r_guards(rnd, spec):
    return r_ceilings(rnd, spec, True)


def r_pillar(rnd, spec):
    R = Room('PILLAR', 12, 18, fdepth=4)
    R.diff = 3
    R.box(15, 4, 15, 11, '#')
    R.put(10, 11, '>')
    R.put(19, 11, '<')
    R.put(14, 8, 'o'), R.put(14, 6, 'o'), R.put(16, 8, 'o')
    R.hint = ('SIDEWAYS GRAVITY! PRESS UP TO CLIMB.', 9, 8)
    return R


def r_springs(rnd, spec):
    R = Room('SPRINGS', 12, 20, fdepth=3)
    R.diff = 2
    R.put(9, 11, 'S')
    R.box(11, 7, 14, 7, '#')
    R.put(13, 6, 'S')
    R.box(16, 2, 19, 2, '#')
    for c in range(12, 18):
        R.put(c, 11, 'u')
    R.put(12, 5, 'o'), R.put(17, 1, 'o')
    R.hint = ('SPRINGS LAUNCH YOU.', 9, 8)
    return R


def r_crumble(rnd, spec):
    R = Room('CRUMBLE', 9, 23)
    R.diff = 3
    R.box(0, 0, 1, 8, '#')
    for c in range(9, 22):
        R.put(c, 8, 'u')
    for (a, b) in ((9, 11), (14, 16), (19, 21)):
        for c in range(a, b + 1):
            R.put(c, 7, 'c')
    R.put(12, 5, 'o'), R.put(17, 5, 'o'), R.put(10, 5, 'o')
    R.cp = 2
    R.hint = ('CRACKED STONE CRUMBLES. KEEP MOVING.', 9, 4)
    return R


def r_windrun(rnd, spec):
    R = Room('WINDRUN', 10, 22)
    R.diff = 3
    for r in range(3, 9):
        for c in range(8, 22):
            R.put(c, r, '4')
    R.box(13, 5, 13, 9, '#')
    R.box(17, 0, 17, 5, '#')
    R.put(10, 5, 'o'), R.put(15, 7, 'o'), R.put(19, 7, 'o')
    R.hint = ('JUMP INTO THE WIND. IT CARRIES YOU.', 9, 4)
    return R


def r_flipflop(rnd, spec):
    R = Room('FLIPFLOP', 9, 24)
    R.diff = 4
    R.box(1, 0, 2, 8, '#')
    for c in (8, 9, 10):
        R.put(c, 0, 'd')
    for c in range(13, 17):
        R.put(c, 8, 'u')
    for c in range(20, 24):
        R.put(c, 8, 'u')
    R.put(12, 8, '^')
    R.put(17, 0, 'v')
    R.put(19, 8, '^')
    R.put(14, 1, 'o'), R.put(15, 1, 'o'), R.put(22, 1, 'o')
    R.cp = 3
    return R


def r_spiral(rnd, spec):
    R = Room('SPIRAL', 14, 3, fdepth=4)
    R.diff = 3
    for i in range(1, 7):
        r = 14 - 2 * i
        c0 = 8 + 4 * (i - 1)
        for k in range(3):
            R.put(c0 + k, r, '#')
    for c in range(11, 28):
        R.put(c, 13, 'u')
    for c in (0, 1, 2):
        R.put(c, 13, 'u')
    R.cp = None
    R.put(17, 7, 'C')
    R.put(9, 11, 'o'), R.put(13, 9, 'o'), R.put(21, 5, 'o'), R.put(25, 3, 'o')
    R.hint = ('CLIMB ROUND THE TOWER.', 9, 9)
    return R


def r_carousel(rnd, spec):
    R = Room('CAROUSEL', 10, 16)
    R.diff = 1
    for r in range(4, 9):
        for c in list(range(0, 16)) + list(range(20, 28)):
            R.put(c, r, '4')
    for c in list(range(8, 16)) + list(range(20, 28)):
        R.put(c, 9, 'u')
    R.put(10, 5, 'o'), R.put(13, 7, 'o'), R.put(23, 6, 'o'), R.put(26, 5, 'o')
    R.cp = None
    R.hint = ('THE TOWER TURNS. RIDE THE WIND.', 9, 2)
    return R


ROOMS = {
    'START': r_start, 'END': r_end, 'HALL': r_hall, 'DOORS': r_doors,
    'CEILINGS': r_ceilings, 'GUARDS': r_guards, 'PILLAR': r_pillar,
    'SPRINGS': r_springs, 'CRUMBLE': r_crumble, 'WINDRUN': r_windrun,
    'FLIPFLOP': r_flipflop, 'SPIRAL': r_spiral, 'CAROUSEL': r_carousel,
}
POOL = ['HALL', 'CAROUSEL', 'DOORS', 'CEILINGS', 'SPRINGS', 'PILLAR', 'SPIRAL',
        'WINDRUN', 'CRUMBLE', 'GUARDS', 'FLIPFLOP']
POOL_DIFF = {'HALL': 1, 'CAROUSEL': 1, 'DOORS': 2, 'CEILINGS': 2, 'SPRINGS': 2, 'PILLAR': 3,
             'SPIRAL': 3, 'WINDRUN': 3, 'CRUMBLE': 3, 'GUARDS': 3, 'FLIPFLOP': 4}


def sprinkle(room, rnd, n_wisp, n_saw):
    """Add orbiting wisps (mid-air) and floor/ceiling saws in open space."""
    H = room.H
    ecen = room.entry + 1.5
    xcen = None if room.exit is None else room.exit + 1.5
    placed = 0
    rows = [r for r in (4, H - 5) if 3 <= r <= H - 4]
    for _ in range(80):
        if placed >= n_wisp or not rows:
            break
        c = rnd.randrange(RW)
        rr = rnd.choice(rows)
        if cdist(c, ecen) < 6.5 or (xcen is not None and cdist(c, xcen) < 6.5):
            continue
        ok = all(room.get(c + dc, r) == '.' for dc in range(-3, 4)
                 for r in range(max(0, rr - 3), min(H, rr + 4)))
        if ok:
            room.put(c, rr, 'W')
            placed += 1
    placed = 0
    for _ in range(80):
        if placed >= n_saw:
            break
        c = rnd.randrange(RW)
        side = rnd.choice('fc')
        if cdist(c, ecen) < 5 or (xcen is not None and cdist(c, xcen) < 5):
            continue
        rows_l = range(H - 3, H) if side == 'f' else range(0, 3)
        ok = all(room.get(c + dc, r) == '.' for dc in range(-4, 5) for r in rows_l)
        if ok:
            room.saws.append(dict(col=c, row=H - 1 if side == 'f' else 0, half=36,
                                  axis='h', side=side))
            placed += 1


# ============================================================================
#  LEVEL   (stacks rooms into a tower; optional upside-down tower)
# ============================================================================
class Level:
    def __init__(self, spec):
        self.spec = spec
        self.name = spec['name']
        self.sub = spec.get('sub', '')
        self.theme = spec.get('theme', 0)
        self.inverted = bool(spec.get('inv', False))
        self.par = spec.get('par', 120)
        self.hints_on = bool(spec.get('hints', False))
        self.W = RW
        self.ring = True
        self.kind = 'tower'
        self.ents = []
        self.build()

    # -- build --------------------------------------------------------------
    def build(self):
        sp = self.spec
        rnd = random.Random(sp['seed'])
        rooms = []
        for i, nm in enumerate(sp['rooms']):
            r = ROOMS[nm](rnd, sp)
            if nm not in ('START', 'END') and (sp.get('wisps', 0) or sp.get('saws', 0)):
                sprinkle(r, rnd, sp.get('wisps', 0), sp.get('saws', 0))
            if not sp.get('fixed') and rnd.random() < 0.5:
                r = r.mirrored()
            rooms.append(r)
        n = len(rooms)
        shifts = [0 if sp.get('fixed') else rnd.randrange(RW)]
        for i in range(1, n):
            px = (rooms[i - 1].exit + shifts[i - 1]) % RW
            shifts.append((px - rooms[i].entry) % RW)
        Hs = [r.H for r in rooms]
        R = sum(Hs) + SLAB * (n + 1)
        self.R = R
        self.wpx, self.hpx = RW * TILE, R * TILE
        g = [[0] * RW for _ in range(R)]
        self.g = g
        tops = [0] * n
        y = SLAB
        for k in range(n - 1, -1, -1):
            tops[k] = y
            y += Hs[k] + SLAB
        for rr in range(R):
            pass
        for rr in (0, 1):
            g[rr] = [1] * RW
        for k in range(n):
            for rr in (tops[k] + Hs[k], tops[k] + Hs[k] + 1):
                g[rr] = [1] * RW
        self.room_names = [r.name for r in rooms]
        self.bounds = [(tops[k], tops[k] + Hs[k] - 1) for k in range(n)]
        fieldmap = {}
        for k in range(1, n):
            cols = [(rooms[k].entry + shifts[k] + i) % RW for i in range(HWID)]
            for rr in (tops[k] + Hs[k], tops[k] + Hs[k] + 1):
                for c in cols:
                    g[rr][c] = 0
            lo = tops[k] + Hs[k] - 2
            hi = tops[k - 1] + rooms[k - 1].fdepth - 1
            for rr in range(lo, hi + 1):
                for c in cols:
                    fieldmap[(rr, c)] = (UP, True)
        self.holefield_rows = None
        self.crystals, self.springs, self.souls, self.cps = [], [], [], []
        self.orbits, self.saws = [], []
        self.hints = []
        seen_hint = set()
        spring_cells = []
        cmap = {'^': UP, 'v': DOWN, '<': LEFT, '>': RIGHT}
        fmap = {'1': UP, '2': DOWN, '3': LEFT, '4': RIGHT}
        smap = {'u': 2, 'd': 3, 'l': 4, 'r': 5}
        for k, room in enumerate(rooms):
            sh = shifts[k]
            H = room.H
            if room.cp is not None and 0 < k < n - 1 and k % 2 == 1:
                if room.get(room.cp, H - 1) == '.':
                    room.put(room.cp, H - 1, 'C')
            for r in range(H):
                for c in range(RW):
                    ch = room.cells[r][c]
                    if ch == '.':
                        continue
                    gr, gc = tops[k] + r, (c + sh) % RW
                    if ch == '#':
                        g[gr][gc] = 1
                    elif ch == 'c':
                        g[gr][gc] = 6
                    elif ch in smap:
                        g[gr][gc] = smap[ch]
                    elif ch in cmap:
                        self.crystals.append(dict(c=gc, r=gr, d=cmap[ch]))
                    elif ch in fmap:
                        fieldmap.setdefault((gr, gc), (fmap[ch], False))
                    elif ch == 'o':
                        self.souls.append(dict(c=gc, r=gr))
                    elif ch == 'S':
                        spring_cells.append((gr, gc))
                    elif ch == 'C':
                        self.cps.append(dict(c=gc, r=gr))
                    elif ch == 'W':
                        w = rnd.uniform(0.028, 0.04) * rnd.choice((-1, 1))
                        ph = rnd.uniform(0, math.pi * 2)
                        for q in range(max(1, sp.get('wisps', 1) if sp.get('wisps') else 1)):
                            self.orbits.append(dict(cx=gc * TILE + 8, cy=gr * TILE + 8,
                                                    rx=2.4 * TILE, ry=1.8 * TILE, w=w,
                                                    ph=ph + q * math.pi))
            for e in room.ents:
                self.ents.append(dict(e, c=(e['c'] + sh) % RW, r=tops[k] + e['r']))
            for s in room.saws:
                gc = (s['col'] + sh) % RW
                gr = tops[k] + s['row']
                cy = (gr + 1) * TILE - 6 if s['side'] == 'f' else gr * TILE + 6
                self.saws.append(dict(cx=gc * TILE + 8, cy=cy, half=s['half'], axis='h',
                                      w=rnd.uniform(0.03, 0.045) * rnd.choice((-1, 1)),
                                      ph=rnd.uniform(0, 6.28)))
            if room.hint and room.name not in seen_hint:
                seen_hint.add(room.name)
                self.hints.append(dict(x=((room.hint[1] + sh) % RW) * TILE + 8,
                                       y=(tops[k] + room.hint[2]) * TILE, text=room.hint[0],
                                       room=True))
        # springs: face away from the surface they sit on
        for (r, c) in spring_cells:
            def solid(rr, cc):
                return 0 <= rr < R and g[rr][cc % RW] in (1, 6)
            if solid(r + 1, c):
                d = UP
            elif solid(r - 1, c):
                d = DOWN
            elif solid(r, c - 1):
                d = RIGHT
            elif solid(r, c + 1):
                d = LEFT
            else:
                d = UP
            self.springs.append(dict(c=c, r=r, d=d))
        # spawn / door
        r0 = rooms[0]
        self.spawn = (((r0.start + shifts[0]) % RW) * TILE + 2, (tops[0] + Hs[0]) * TILE - PS)
        rl = rooms[-1]
        self.door = (((rl.door + shifts[-1]) % RW) * TILE, (tops[-1] + Hs[-1]) * TILE - 32)
        for i, t in enumerate(sp.get('start_hints', [])):
            self.hints.append(dict(x=self.spawn[0] + 6, y=self.spawn[1] - 56 + i * 9,
                                   text=t, room=False))
        self.default_g = DOWN
        self.fieldmap = fieldmap
        if self.inverted:
            self.invert()
        self.finish()

    # -- upside-down tower: rotate everything 180 degrees ----------------------
    def invert(self):
        R, W = self.R, RW
        wpx, hpx = self.wpx, self.hpx
        mv = {0: 0, 1: 1, 2: 3, 3: 2, 4: 5, 5: 4, 6: 6}
        g2 = [[0] * RW for _ in range(R)]
        for r in range(R):
            for c in range(RW):
                g2[R - 1 - r][RW - 1 - c] = mv[self.g[r][c]]
        self.g = g2
        for cr in self.crystals:
            cr['c'], cr['r'], cr['d'] = RW - 1 - cr['c'], R - 1 - cr['r'], OPP[cr['d']]
        for sp in self.springs:
            sp['c'], sp['r'], sp['d'] = RW - 1 - sp['c'], R - 1 - sp['r'], OPP[sp['d']]
        for s in self.souls:
            s['c'], s['r'] = RW - 1 - s['c'], R - 1 - s['r']
        for s in self.cps:
            s['c'], s['r'] = RW - 1 - s['c'], R - 1 - s['r']
        self.fieldmap = {(R - 1 - r, RW - 1 - c): (OPP[d], rs)
                         for (r, c), (d, rs) in self.fieldmap.items()}
        for o in self.orbits:
            o['cx'], o['cy'], o['ph'] = wpx - o['cx'], hpx - o['cy'], o['ph'] + math.pi
        for o in self.saws:
            o['cx'], o['cy'], o['ph'] = wpx - o['cx'], hpx - o['cy'], o['ph'] + math.pi
        for h in self.hints:
            h['x'], h['y'] = wpx - h['x'], hpx - h['y']
        self.spawn = (wpx - self.spawn[0] - PS, hpx - self.spawn[1] - PS)
        self.door = (wpx - self.door[0] - 16, hpx - self.door[1] - 32)
        self.bounds = [(R - 1 - b, R - 1 - a) for (a, b) in self.bounds]
        self.default_g = UP

    # -- derived data -----------------------------------------------------------
    def finish(self):
        R = self.R
        g = self.g
        for cr in self.crystals:
            cr['x'], cr['y'] = cr['c'] * TILE, cr['r'] * TILE
        for sp in self.springs:
            sp['x'], sp['y'] = sp['c'] * TILE, sp['r'] * TILE
        for s in self.souls:
            s['x'], s['y'] = s['c'] * TILE + 4, s['r'] * TILE + 4
        for cp in self.cps:
            cp['x'], cp['y'] = cp['c'] * TILE, cp['r'] * TILE
            if self.inverted:
                cp['rx'], cp['ry'] = cp['c'] * TILE + 2, cp['r'] * TILE
            else:
                cp['rx'], cp['ry'] = cp['c'] * TILE + 2, (cp['r'] + 1) * TILE - PS
        self.respawn = self.spawn
        for e in self.ents:
            e['x'], e['y'] = e['c'] * TILE, e['r'] * TILE
        W = self.W
        self.deco = [[None] * W for _ in range(R)]
        rows_room = set()
        for (a, b) in self.bounds:
            rows_room.update(range(a, b + 1))
        ring = self.ring

        def cell(r, c):
            if r < 0 or r >= R:
                return 1
            if ring:
                return g[r][c % W]
            return g[r][c] if 0 <= c < W else 1
        for r in range(R):
            for c in range(W):
                if g[r][c] not in (1, 6):
                    continue
                var = (r * 7 + c * 13) % 3
                top = not self.solid(r - 1, c)
                bot = not self.solid(r + 1, c)
                rune = (r not in rows_room) and (cell(r, c - 1) == 0 or cell(r, c + 1) == 0)
                self.deco[r][c] = (var, top, bot, rune)
        dr = random.Random(self.spec['seed'] + 99)
        self.windows, self.torches, self.chains = [], [], []
        for (a, b) in self.bounds:
            H = b - a + 1
            if H < 7:
                continue
            o = dr.randrange(8)
            for c in range(o, W, 8):
                if ring or c + 3 <= W:
                    if all(cell(r, c + k) == 0 for r in range(a + 1, a + 5) for k in range(3)):
                        self.windows.append((c * TILE, a * TILE + 24))
                tc = c + 4
                if (ring or tc < W) and all(cell(r, tc) == 0 for r in range(a + 2, a + 4)):
                    self.torches.append(((tc % W) * TILE + 4, (a + 2) * TILE))
            for _ in range(3):
                c = dr.randrange(W)
                ln = dr.randint(2, 4)
                if a >= 1 and g[a - 1][c] == 1 and all(cell(a + i, c) == 0 for i in range(ln)):
                    self.chains.append((c * TILE + 5, a * TILE, ln))
        self.hints = [h for h in self.hints if (not h['room']) or self.hints_on]

    def solid(self, r, c):
        if r < 0 or r >= self.R:
            return True
        if not self.ring and (c < 0 or c >= self.W):
            return True
        return self.g[r][c % self.W] in (1, 6)

    def wd(self, d):
        """signed horizontal distance (shortest way round if the level is a ring)"""
        return wrapd(d, self.wpx) if self.ring else d

    # -- dynamic hazards ----------------------------------------------------
    def movers(self, t):
        out = []
        for o in self.orbits:
            a = o['ph'] + o['w'] * t
            out.append((o['cx'] + o['rx'] * math.cos(a), o['cy'] + o['ry'] * math.sin(a), 3.5))
        for s in self.saws:
            p = s['half'] * math.sin(s['ph'] + s['w'] * t)
            if s.get('axis') == 'v':
                out.append((s['cx'], s['cy'] + p, 5.5))
            else:
                out.append((s['cx'] + p, s['cy'], 5.5))
        return out

    def spike_hit(self, x, y, w, h):
        c0 = int(x // TILE)
        c1 = int((x + w - 0.001) // TILE)
        r0 = max(0, int(y // TILE))
        r1 = min(self.R - 1, int((y + h - 0.001) // TILE))
        g = self.g
        for r in range(r0, r1 + 1):
            row = g[r]
            for ci in range(c0, c1 + 1):
                if not self.ring and (ci < 0 or ci >= self.W):
                    continue
                v = row[ci % self.W]
                if v < 2 or v > 5:
                    continue
                bx, by = ci * TILE, r * TILE
                if v == 2:
                    sx, sy, sw, sh = bx, by + 9, 16, 7
                elif v == 3:
                    sx, sy, sw, sh = bx, by, 16, 7
                elif v == 4:
                    sx, sy, sw, sh = bx + 9, by, 7, 16
                else:
                    sx, sy, sw, sh = bx, by, 7, 16
                if x < sx + sw and x + w > sx and y < sy + sh and y + h > sy:
                    return True
        return False


# ============================================================================
#  CAMPAIGN  +  PROCEDURAL SPECS
# ============================================================================
def L(name, sub, theme, rooms, seed, par, inv=False, hints=False, **kw):
    d = dict(name=name, sub=sub, theme=theme, rooms=['START'] + rooms + ['END'],
             seed=seed, par=par, inv=inv, hints=hints)
    d.update(kw)
    return d


LEVELS = [
    L('THE FOYER', 'CLIMB. THE TOWER TURNS.', 0, ['HALL', 'DOORS', 'HALL'], 101, 60, hints=True,
      start_hints=['A D MOVE   SPACE JUMP', 'THE TOWER IS A RING. WALK ROUND IT.']),
    L('THE WINDING WAY', 'RIDE THE WIND ROUND.', 0, ['CAROUSEL', 'SPRINGS', 'DOORS'], 102, 75,
      hints=True),
    L('THE UPSIDE-DOWN STAIR', 'DESCEND. THE FLOOR IS ABOVE YOU.', 0, ['HALL', 'CEILINGS', 'DOORS'],
      103, 85, inv=True, hints=True,
      start_hints=['THIS TOWER IS UPSIDE DOWN.', 'YOUR FEET STICK TO THE CEILING.']),
    L('BONE GALLERY', 'CLIMB. THE WALLS HAVE GRAVITY TOO.', 1, ['CEILINGS', 'PILLAR', 'HALL', 'SPRINGS'],
      104, 110, hints=True),
    L('THE OSSUARY', 'CLIMB. CRYSTALS EVERYWHERE.', 1, ['PILLAR', 'DOORS', 'CRUMBLE', 'SPIRAL'], 105, 130),
    L('THE HANGING CRYPT', 'DESCEND. HANG ON.', 1, ['SPIRAL', 'PILLAR', 'CEILINGS', 'CRUMBLE'], 106, 140,
      inv=True),
    L('THE BELLOWS', 'CLIMB. THE WIND DECIDES.', 2, ['WINDRUN', 'CRUMBLE', 'DOORS', 'SPRINGS'], 107, 130),
    L('THE SMELTERY', 'CLIMB. SAWS AND FLAMES.', 2, ['CEILINGS', 'WINDRUN', 'SPIRAL', 'PILLAR', 'CRUMBLE'],
      108, 170, saws=1),
    L('THE MOLTEN DROP', 'DESCEND. LET GO.', 2, ['FLIPFLOP', 'SPRINGS', 'WINDRUN', 'DOORS'], 109, 160,
      inv=True),
    L('THE ICE WELL', 'CLIMB. SLIP AND SLIDE.', 3, ['SPRINGS', 'PILLAR', 'WINDRUN', 'DOORS', 'SPIRAL'],
      110, 190),
    L('THE FROZEN FALL', 'DESCEND. DO NOT STOP.', 3, ['CRUMBLE', 'FLIPFLOP', 'PILLAR', 'WINDRUN'], 111, 190,
      inv=True, saws=1),
    L('THE GLASS SPIRE', 'CLIMB. WISPS DANCE IN THE COLD.', 3,
      ['GUARDS', 'SPIRAL', 'PILLAR', 'CRUMBLE', 'FLIPFLOP'], 112, 230, wisps=1),
    L('THE EDGE OF NOTHING', 'CLIMB. UP IS A MATTER OF OPINION.', 4,
      ['FLIPFLOP', 'SPIRAL', 'PILLAR', 'GUARDS', 'CRUMBLE'], 113, 250, wisps=1),
    L('THE FALLING STAIR', 'DESCEND INTO THE DARK.', 4, ['PILLAR', 'WINDRUN', 'FLIPFLOP', 'SPIRAL', 'DOORS'],
      114, 250, inv=True, saws=1),
    L('THE HOLLOW CROWN', 'CLIMB. THE VOID WATCHES.', 4,
      ['CRUMBLE', 'GUARDS', 'FLIPFLOP', 'PILLAR', 'SPIRAL', 'WINDRUN'], 115, 300, wisps=1, saws=1),
    L('THE GEAR VAULT', 'CLIMB. EVERYTHING TURNS.', 5, ['DOORS', 'WINDRUN', 'FLIPFLOP', 'SPIRAL', 'PILLAR'],
      116, 300, wisps=1, saws=1),
    L('THE UPSIDE CLOCK', 'DESCEND. TIME RUNS BACKWARDS.', 5,
      ['CRUMBLE', 'GUARDS', 'PILLAR', 'FLIPFLOP', 'WINDRUN', 'SPIRAL'], 117, 340, inv=True, wisps=1,
      saws=1),
    L('THE ENDLESS RING', 'CLIMB. THE LAST TURN.', 5,
      ['FLIPFLOP', 'SPIRAL', 'GUARDS', 'PILLAR', 'CRUMBLE', 'WINDRUN', 'FLIPFLOP', 'SPIRAL'], 118, 420,
      wisps=2, saws=1),
]

SECTION_SUBS = ['CLIMB.', 'DESCEND.']


def procedural_spec(seed, section, rooms_n=None, diff=None, theme=None, inv=None, name=None):
    """A fresh tower: section 1 is gentle, later sections add rooms, hazards, upside-down floors."""
    rnd = random.Random(seed * 7919 + section * 104729)
    d = diff if diff is not None else 1 + section * 0.55
    n = rooms_n if rooms_n is not None else min(9, 3 + section // 2 + 1)
    rooms = []
    prev = None
    for _ in range(n):
        cands = [r for r in POOL if POOL_DIFF[r] <= d + 0.9 and r != prev]
        w = [1.0 + (POOL_DIFF[r] >= d - 0.5) * 1.5 for r in cands]
        pick = rnd.choices(cands, weights=w)[0]
        rooms.append(pick)
        prev = pick
    th = theme if theme is not None else (section - 1) % len(THEMES)
    iv = inv if inv is not None else (section >= 3 and rnd.random() < 0.4)
    wisps = 1 if d >= 3.2 else 0
    saws = 1 if d >= 2.4 else 0
    return dict(name=name or ('SECTION %d' % section), sub=(SECTION_SUBS[1] if iv else SECTION_SUBS[0]),
                theme=th, rooms=['START'] + rooms + ['END'], seed=rnd.randrange(1, 10 ** 6),
                par=60 + n * 25, inv=iv, hints=False, wisps=wisps, saws=saws)


# ============================================================================
#  SIMULATION  (pure game logic, no tkinter: the game and the test bot share it)
# ============================================================================
class Sim:
    """
    Gravity has four directions.  `base` is set by crystals; fields override it
    while you are inside them.  Movement is along the surface you stand on:
    x when gravity is vertical, y when it is horizontal.
    """

    def __init__(self, lvl, bot=False):
        self.lvl = lvl
        self.bot = bot
        self.t = 0
        self.souls = [False] * len(lvl.souls)
        self.lit = [False] * len(lvl.cps)
        self.crumb = {}
        self.gone = {}
        self.respawn = lvl.spawn
        self.dead = False
        self.inv = 0
        self.W = lvl.W
        self.ring = lvl.ring
        self.ab = set()
        self.reset_player(*lvl.spawn)

    def reset_player(self, x, y):
        self.x, self.y = float(x), float(y)
        self.vx = self.vy = 0.0
        self.base = self.lvl.default_g
        self.eff = self.base
        self.in_field = None
        self.on_ground = False
        self.coyote = 0
        self.buf = 0
        self.cd = 0
        self.scd = 0
        self.jumping = False
        self.face = 1
        self.anim = 0.0
        self.dead = False
        self.air_jumps = 0
        self.dash_t = 0
        self.dash_cd = 0
        self.dash_dir = 1
        self.dashed = False

    # -- snapshots (used by the test bot) -----------------------------------
    def snap(self):
        return (self.x, self.y, self.vx, self.vy, self.base, self.in_field, self.on_ground,
                self.coyote, self.buf, self.cd, self.scd, self.jumping, self.eff)

    def restore(self, s):
        (self.x, self.y, self.vx, self.vy, self.base, self.in_field, self.on_ground,
         self.coyote, self.buf, self.cd, self.scd, self.jumping, self.eff) = s
        self.dead = False

    # -- collision ------------------------------------------------------------
    def _solid(self, r, c):
        lvl = self.lvl
        if r < 0 or r >= lvl.R:
            return True
        if not self.ring and (c < 0 or c >= self.W):
            return True
        v = lvl.g[r][c % self.W]
        if v == 1:
            return True
        if v == 6:
            return (r, c % self.W) not in self.gone
        return False

    def _stand(self, r, c):
        if self.bot:
            return
        if self.lvl.g[r][c % self.W] == 6:
            k = (r, c % self.W)
            if k not in self.crumb:
                self.crumb[k] = CRUMBLE_T

    def _move_x(self):
        self.x += self.vx
        c0 = int(self.x // TILE)
        c1 = int((self.x + PS - 0.001) // TILE)
        r0 = int(self.y // TILE)
        r1 = int((self.y + PS - 0.001) // TILE)
        cols = range(c1, c0 - 1, -1) if self.vx > 0 else range(c0, c1 + 1)
        for r in range(r0, r1 + 1):
            for c in cols:
                if self._solid(r, c):
                    if self.vx > 0:
                        self.x = c * TILE - PS
                        if self.eff == RIGHT:
                            self.on_ground = True
                            self._stand(r, c)
                    elif self.vx < 0:
                        self.x = (c + 1) * TILE
                        if self.eff == LEFT:
                            self.on_ground = True
                            self._stand(r, c)
                    self.vx = 0.0
                    return

    def _move_y(self):
        self.y += self.vy
        c0 = int(self.x // TILE)
        c1 = int((self.x + PS - 0.001) // TILE)
        r0 = int(self.y // TILE)
        r1 = int((self.y + PS - 0.001) // TILE)
        rows = range(r1, r0 - 1, -1) if self.vy > 0 else range(r0, r1 + 1)
        for r in rows:
            for c in range(c0, c1 + 1):
                if self._solid(r, c):
                    if self.vy > 0:
                        self.y = r * TILE - PS
                        if self.eff == DOWN:
                            self.on_ground = True
                            self._stand(r, c)
                    elif self.vy < 0:
                        self.y = (r + 1) * TILE
                        if self.eff == UP:
                            self.on_ground = True
                            self._stand(r, c)
                    self.vy = 0.0
                    return

    # -- one frame ------------------------------------------------------------
    def step(self, lat, jp, jh, dash=False):
        """lat: -1/0/1 along the surface axis; jp: jump pressed this frame; jh: jump held."""
        lvl = self.lvl
        ev = []
        self.t += 1
        fd = self.in_field
        eff = fd if fd is not None else self.base
        self.eff = eff
        vert = eff < 2
        gs = 1 if eff in (DOWN, RIGHT) else -1
        lv = self.vx if vert else self.vy
        gv = self.vy if vert else self.vx
        if lat:
            self.face = lat
            tgt = lat * RUN
            a = ACC_G if self.on_ground else ACC_A
            if lv < tgt:
                lv = min(tgt, lv + a)
            elif lv > tgt:
                lv = max(tgt, lv - a)
        else:
            f = FRC_G if self.on_ground else FRC_A
            if abs(lv) <= f:
                lv = 0.0
            else:
                lv -= f if lv > 0 else -f
        if fd is not None:
            lv *= 0.9
        if self.dash_cd > 0:
            self.dash_cd -= 1
        if dash and self.ab and 'dash' in self.ab and not self.dashed and self.dash_cd <= 0:
            self.dash_t = 9
            self.dash_dir = lat if lat else self.face
            self.dash_cd = 36
            self.dashed = True
            self.jumping = False
            ev.append('dash')
        dashing = self.dash_t > 0
        if dashing:
            self.dash_t -= 1
        if self.cd > 0:
            self.cd -= 1
        if self.scd > 0:
            self.scd -= 1
        if self.inv > 0:
            self.inv -= 1
        if self.on_ground:
            self.coyote = COYOTE
            self.air_jumps = 1
            self.dashed = False
        elif self.coyote > 0:
            self.coyote -= 1
        if jp:
            self.buf = BUFFER
        elif self.buf > 0:
            self.buf -= 1
        if self.buf > 0 and self.coyote > 0:
            gv = -JUMP * gs
            self.buf = 0
            self.coyote = 0
            self.on_ground = False
            self.jumping = True
            ev.append('jump')
        elif jp and self.ab and 'double' in self.ab and self.coyote <= 0 and self.air_jumps > 0:
            gv = -JUMP * 0.92 * gs
            self.air_jumps -= 1
            self.jumping = True
            ev.append('jump2')
        up_speed = -gv * gs
        if self.jumping:
            if up_speed <= 0:
                self.jumping = False
            elif not jh and up_speed > 2.4:
                gv = -2.4 * gs
        gv += GRAV * gs
        mv = FIELD_MAXV if fd is not None else MAXV
        if gv * gs > mv:
            gv = mv * gs
        if dashing:
            gv = 0.0
            lv = self.dash_dir * 5.2
        if lv > MAXV:
            lv = MAXV
        elif lv < -MAXV:
            lv = -MAXV
        if vert:
            self.vx, self.vy = lv, gv
        else:
            self.vx, self.vy = gv, lv
        was_air = not self.on_ground
        pre = gv
        self.on_ground = False
        self._move_x()
        self._move_y()
        if self.ring:
            self.x %= lvl.wpx
        if self.on_ground and was_air and abs(pre) > 2.5:
            ev.append('land')
        self.anim += abs(lv) * 0.12

        cx, cy = self.x + PS / 2.0, self.y + PS / 2.0
        fm = lvl.fieldmap.get((int(cy // TILE), int(cx // TILE) % self.W))
        if fm:
            if self.in_field != fm[0]:
                ev.append(('field', fm[0]))
            self.in_field = fm[0]
            if fm[1]:
                self.base = lvl.default_g
        else:
            self.in_field = None
        wp = lvl.wpx
        if self.cd <= 0:
            for cr in lvl.crystals:
                if abs(lvl.wd(cr['x'] + 8 - cx)) < 9 and abs(cr['y'] + 8 - cy) < 9:
                    if cr['d'] != self.base:
                        self.base = cr['d']
                        self.cd = CRYSTAL_CD
                        self.jumping = False
                        ev.append(('crystal', cr['d']))
                    break
        if self.scd <= 0:
            for sp in lvl.springs:
                if abs(lvl.wd(sp['x'] + 8 - cx)) < 9 and abs(sp['y'] + 8 - cy) < 9:
                    d = sp['d']
                    if d < 2:
                        self.vy = GVEC[d][1] * SPRING_V
                    else:
                        self.vx = GVEC[d][0] * SPRING_V
                    self.scd = SPRING_CD
                    self.air_jumps = 1
                    self.jumping = False
                    self.coyote = 0
                    self.on_ground = False
                    ev.append(('spring', sp))
                    break
        if not self.bot:
            for i, s in enumerate(lvl.souls):
                if not self.souls[i] and abs(lvl.wd(s['x'] + 4 - cx)) < 9 and abs(s['y'] + 4 - cy) < 10:
                    self.souls[i] = True
                    ev.append(('soul', i))
            for i, cp in enumerate(lvl.cps):
                if not self.lit[i] and abs(lvl.wd(cp['x'] + 8 - cx)) < 11 and abs(cp['y'] + 8 - cy) < 14:
                    self.lit[i] = True
                    self.respawn = (cp['rx'], cp['ry'])
                    self.air_jumps = 1
                    ev.append(('cp', i))
            if self.crumb:
                for k in list(self.crumb):
                    self.crumb[k] -= 1
                    if self.crumb[k] <= 0:
                        del self.crumb[k]
                        self.gone[k] = self.t + CRUMBLE_RET
                        ev.append(('crumble', k))
            if self.gone:
                for k in list(self.gone):
                    if self.t >= self.gone[k]:
                        r, c = k
                        if (abs(lvl.wd(c * TILE + 8 - cx)) < 8 + PS / 2.0 and
                                abs(r * TILE + 8 - cy) < 8 + PS / 2.0):
                            self.gone[k] = self.t + 10
                        else:
                            del self.gone[k]
                            ev.append(('mend', k))
            if lvl.door and abs(lvl.wd(lvl.door[0] + 8 - cx)) < 7 and abs(lvl.door[1] + 16 - cy) < 14:
                ev.append('door')
        if self.inv <= 0:
            hit = lvl.spike_hit(self.x + 1, self.y + 1, PS - 2, PS - 2)
            if not hit and not self.bot:
                for (mx, my, rad) in lvl.movers(self.t):
                    dx = lvl.wd(mx - cx)
                    dy = my - cy
                    nx = max(-PS / 2.0 + 1, min(PS / 2.0 - 1, dx))
                    ny = max(-PS / 2.0 + 1, min(PS / 2.0 - 1, dy))
                    if (dx - nx) ** 2 + (dy - ny) ** 2 < rad * rad:
                        hit = True
                        break
            if hit:
                self.dead = True
                ev.append('death')
        return ev


# ============================================================================
#  AUDIO  -  everything is synthesised: sfxr-style effects + generative chiptune
# ============================================================================
SR = 22050
_NOTE_CACHE = {}


def midi_hz(m):
    return 440.0 * 2.0 ** ((m - 69) / 12.0)


def note_wave(kind, freq, n, vol, duty=0.5, vib=0.0, dec=2.0):
    key = (kind, round(freq, 2), n, round(vol, 3), duty, vib, dec)
    w = _NOTE_CACHE.get(key)
    if w is not None:
        return w
    out = [0] * n
    ph = 0.0
    an = max(1, int(0.004 * SR))
    twopi = 6.283185307
    for i in range(n):
        f = freq * (1 + vib * math.sin(twopi * 5.5 * i / SR)) if vib else freq
        ph += f / SR
        if ph >= 1.0:
            ph -= 1.0
        if kind == 'sq':
            s = 1.0 if ph < duty else -1.0
        elif kind == 'tri':
            s = 4 * ph - 1 if ph < 0.5 else 3 - 4 * ph
        elif kind == 'saw':
            s = 2 * ph - 1
        else:
            s = math.sin(twopi * ph)
        e = (i / an if i < an else 1.0) * (1.0 - i / n) ** dec
        out[i] = int(s * e * vol)
    if len(_NOTE_CACHE) > 600:
        _NOTE_CACHE.clear()
    _NOTE_CACHE[key] = out
    return out


def noise_wave(n, vol, dec=3.0, hold=1, seed=1):
    rnd = random.Random(seed)
    out = [0] * n
    cur = 0.0
    for i in range(n):
        if i % hold == 0:
            cur = rnd.random() * 2 - 1
        out[i] = int(cur * vol * (1.0 - i / n) ** dec)
    return out


def kick_wave(n, vol):
    out = [0] * n
    ph = 0.0
    for i in range(n):
        f = 45 + 110 * (1.0 - i / n) ** 3
        ph += f / SR
        out[i] = int(math.sin(6.283185 * ph) * vol * (1.0 - i / n) ** 1.5)
    return out


def mix_into(buf, wave_, off):
    n = len(buf)
    if off >= n:
        return
    lim = min(len(wave_), n - off)
    for i in range(lim):
        buf[off + i] += wave_[i]


SCALES = {
    'minor': [0, 2, 3, 5, 7, 8, 10], 'dorian': [0, 2, 3, 5, 7, 9, 10],
    'phrygian': [0, 1, 3, 5, 7, 8, 10], 'harmonic': [0, 2, 3, 5, 7, 8, 11],
}
PROGS = [[0, 5, 2, 6], [0, 3, 4, 0], [0, 6, 5, 6], [0, 2, 5, 4], [0, 5, 3, 4], [0, 4, 5, 3],
         [0, 6, 2, 6], [0, 5, 6, 4]]
BASS_PATS = ['x...x...x...x...', 'x..x..x.x..x..x.', 'x.x.x.x.x.x.x.x.',
             'x...x.x.x...x.x.', 'x.......x.......']
RHYTHMS = [[(0, 4), (4, 2), (6, 2), (8, 4), (12, 4)],
           [(0, 2), (2, 2), (4, 4), (8, 2), (10, 2), (12, 4)],
           [(0, 6), (6, 2), (8, 6), (14, 2)],
           [(0, 3), (3, 3), (6, 2), (8, 4), (12, 2), (14, 2)]]
ARPS = [[0, 1, 2, 1], [0, 2, 1, 2], [0, 1, 2, 3], [2, 1, 0, 1]]
MOODS = {
    'title': dict(bpm=(84, 92), scales=['minor'], duty=0.25, drums=0.6, arp=0.8),
    'foyer': dict(bpm=(92, 104), scales=['minor', 'dorian'], duty=0.25, drums=0.8, arp=1.0),
    'catacomb': dict(bpm=(84, 96), scales=['phrygian', 'minor'], duty=0.125, drums=0.7, arp=1.0),
    'furnace': dict(bpm=(108, 124), scales=['phrygian', 'harmonic'], duty=0.5, drums=1.2, arp=0.9),
    'frost': dict(bpm=(88, 100), scales=['dorian'], duty=0.25, drums=0.6, arp=1.2),
    'void': dict(bpm=(96, 112), scales=['harmonic', 'phrygian'], duty=0.125, drums=0.9, arp=1.0),
    'clock': dict(bpm=(110, 128), scales=['minor', 'harmonic'], duty=0.25, drums=1.1, arp=1.1),
    'endless': dict(bpm=(100, 126), scales=['minor', 'dorian', 'harmonic', 'phrygian'],
                    duty=0.25, drums=1.0, arp=1.0),
}


def gen_music(seed, mood):
    """Structured, seed-deterministic chiptune: A A' B A' over 16 bars."""
    P = MOODS.get(mood, MOODS['foyer'])
    rnd = random.Random(seed * 31 + len(mood))
    bpm = rnd.randrange(P['bpm'][0], P['bpm'][1] + 1, 2)
    step = 60.0 / bpm / 4.0
    spn = int(step * SR)
    bars = 16
    total = spn * 16 * bars
    buf = [0] * total
    scale = SCALES[rnd.choice(P['scales'])]
    root = 36 + rnd.randrange(0, 8)
    progA = rnd.choice(PROGS)
    progB = rnd.choice([p for p in PROGS if p != progA])
    bass_pat = rnd.choice(BASS_PATS)
    arp_pat = rnd.choice(ARPS)
    rh = [rnd.choice(RHYTHMS) for _ in range(2)]

    def pc(deg):
        return scale[deg % 7] + 12 * (deg // 7)

    def chord(deg):
        return [pc(deg), pc(deg + 2), pc(deg + 4), pc(deg) + 12]

    def make_phrase(chords):
        motif = []
        deg = rnd.choice([0, 2, 4]) + 7
        notes0 = rh[0]
        for i, (s, ln) in enumerate(notes0):
            motif.append((s, ln, deg))
            deg += rnd.choices([-2, -1, 0, 1, 2], weights=[2, 3, 1, 3, 2])[0]
            deg = max(4, min(15, deg))
        return motif

    motifA = make_phrase(None)
    motifB = make_phrase(None)

    def lead_bar(bi, sec, prog):
        cd = prog[bi % 4]
        motif = motifA if sec != 'B' else motifB
        shift = [0, 1, 0, -1][bi % 4] if sec != 'B' else [0, 2, 1, 0][bi % 4]
        out = []
        for k, (s, ln, dg) in enumerate(motif):
            d = dg + shift
            if s == 0 or k == len(motif) - 1:
                tones = [cd, cd + 2, cd + 4, cd + 7, cd + 9, cd + 11]
                d = min(tones, key=lambda t: abs(t - d))
            if bi % 4 == 3 and k == len(motif) - 1:
                d = cd + 4
                ln = 4
            out.append((s, ln, d))
        return out

    sections = ['A'] * 4 + ['A2'] * 4 + ['B'] * 4 + ['A3'] * 4
    for bar in range(bars):
        sec = sections[bar]
        prog = progB if sec == 'B' else progA
        deg = prog[bar % 4]
        base = bar * 16 * spn
        ch = chord(deg)
        time.sleep(0.002)
        # bass
        for s in range(16):
            if bass_pat[s] == 'x':
                m = root + pc(deg) + (12 if (s % 8 in (3, 6) and sec != 'A') else 0)
                w = note_wave('tri', midi_hz(m), int(spn * (3 if s % 4 == 0 else 2)), 5200, dec=1.2)
                mix_into(buf, w, base + s * spn)
        # arpeggio
        if sec in ('A', 'A2', 'B', 'A3'):
            vol = 1500 * P['arp'] * (0.7 if sec == 'A' else 1.0)
            for s in range(16):
                if sec == 'A' and s % 2:
                    continue
                m = root + 24 + ch[arp_pat[s % 4] % 4]
                w = note_wave('sq', midi_hz(m), int(spn * 1.6), vol, duty=0.25, dec=2.2)
                mix_into(buf, w, base + s * spn)
        # lead
        if sec != 'A':
            for (s, ln, d) in lead_bar(bar, sec, progB if sec == 'B' else progA):
                m = root + 36 + pc(d)
                dur = int(spn * ln * 0.92)
                w = note_wave('sq', midi_hz(m), dur, 2700, duty=P['duty'],
                              vib=0.004 if ln >= 3 else 0.0, dec=1.0)
                mix_into(buf, w, base + s * spn)
        # drums
        dv = P['drums']
        for s in range(16):
            off = base + s * spn
            if s in (0, 8) or (s == 10 and sec in ('A3', 'B')):
                mix_into(buf, kick_wave(int(spn * 2.2), 7000 * dv), off)
            if s in (4, 12) and sec != 'A':
                mix_into(buf, noise_wave(int(spn * 2.4), 3400 * dv, 2.5, 3, seed + s), off)
            if s % 2 == 0 and not (sec == 'A' and s % 4):
                mix_into(buf, noise_wave(int(spn * 0.8), 1500 * dv, 4.0, 1, seed + 99), off)
    out = array.array('h', [max(-30000, min(30000, v)) for v in buf])
    return out


# ---- sfxr-style effects --------------------------------------------------------
def sfxr(kind='sq', f0=440.0, f1=None, dur=0.15, duty=0.5, dec=1.5, vib=0.0, vibf=0.0,
         arp=None, arp_t=0.5, vol=9000, bits=0, noise=0.0, seed=3):
    n = max(1, int(dur * SR))
    f1 = f0 if f1 is None else f1
    rnd = random.Random(seed)
    out = [0] * n
    ph = 0.0
    hold = 0.0
    an = max(1, int(0.003 * SR))
    for i in range(n):
        fr = i / float(n)
        f = f0 + (f1 - f0) * fr
        if arp and fr > arp_t:
            f *= arp
        if vib:
            f *= 1 + vib * math.sin(6.283 * vibf * i / SR)
        ph += f / SR
        if ph >= 1.0:
            ph -= 1.0
            hold = rnd.random() * 2 - 1
        if kind == 'sq':
            s = 1.0 if ph < duty else -1.0
        elif kind == 'tri':
            s = 4 * ph - 1 if ph < 0.5 else 3 - 4 * ph
        elif kind == 'saw':
            s = 2 * ph - 1
        elif kind == 'noise':
            s = hold
        else:
            s = math.sin(6.283 * ph)
        if noise:
            s = s * (1 - noise) + hold * noise
        e = (i / an if i < an else 1.0) * (1.0 - fr) ** dec
        v = s * e
        if bits:
            q = 2 ** bits
            v = round(v * q) / float(q)
        out[i] = int(v * vol)
    return out


def chain(*parts):
    r = []
    for p in parts:
        r += p
    return r


def _arp(freqs, each=0.07, vol=8000, kind='sq', last=0.18):
    parts = []
    for i, f in enumerate(freqs):
        parts.append(sfxr(kind, f, f, last if i == len(freqs) - 1 else each, 0.5, 1.2, vol=vol))
    return chain(*parts)


SFX_DEFS = {
    'jump': lambda: sfxr('sq', 280, 640, 0.13, 0.35, 1.2, vol=7000),
    'land': lambda: sfxr('noise', 160, 60, 0.07, dec=2.0, vol=5000),
    'spring': lambda: sfxr('sq', 200, 1000, 0.2, 0.5, 1.0, vib=0.02, vibf=18, vol=7000),
    'soul': lambda: _arp([988, 1319], 0.05, 6500, last=0.14),
    'death': lambda: sfxr('sq', 420, 40, 0.45, 0.5, 1.0, noise=0.5, vol=8000),
    'check': lambda: _arp([523, 659, 784], 0.06, 7000, last=0.2),
    'clear': lambda: _arp([523, 659, 784, 1047, 1319], 0.08, 7500, last=0.4),
    'crumble': lambda: sfxr('noise', 110, 70, 0.3, dec=1.2, vol=4500),
    'field': lambda: sfxr('sin', 220, 420, 0.18, dec=1.5, vol=5000),
    'menu': lambda: sfxr('sq', 660, 660, 0.04, 0.5, 1.0, vol=5000),
    'ok': lambda: _arp([784, 1047], 0.04, 6000, last=0.1),
    'back': lambda: sfxr('sq', 440, 330, 0.07, 0.5, 1.0, vol=5000),
    'reset': lambda: sfxr('sq', 320, 90, 0.2, 0.5, 1.0, vol=6500),
    'crystal_up': lambda: _arp([523, 784, 1047], 0.04, 7000, kind='sq', last=0.12),
    'crystal_down': lambda: _arp([1047, 784, 523], 0.04, 7000, kind='sq', last=0.12),
    'crystal_left': lambda: _arp([784, 659, 523, 392], 0.035, 6500, kind='tri', last=0.12),
    'crystal_right': lambda: _arp([392, 523, 659, 784], 0.035, 6500, kind='tri', last=0.12),
    'life': lambda: _arp([659, 784, 988, 1319, 1568], 0.06, 7000, last=0.25),
    'gameover': lambda: _arp([392, 349, 311, 262, 196], 0.14, 7500, kind='tri', last=0.5),
    'star': lambda: _arp([1047, 1319], 0.08, 6500, last=0.2),
}


def write_wav(path, samples):
    arr = samples if isinstance(samples, array.array) else array.array(
        'h', [max(-32000, min(32000, int(v))) for v in samples])
    with wave.open(path, 'wb') as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(SR)
        w.writeframes(arr.tobytes())


# ---- playback backends ----------------------------------------------------------
class _WinBackend:
    def __init__(self):
        import ctypes
        self.mci = ctypes.windll.winmm.mciSendStringW
        self.buf = ctypes.create_unicode_buffer(256)
        self.opened = set()

    def cmd(self, s):
        return self.mci(s, self.buf, 255, 0)

    def open(self, alias, path):
        if alias in self.opened:
            self.close(alias)
        if self.cmd('open "%s" type waveaudio alias %s' % (path, alias)) == 0:
            self.opened.add(alias)
            return True
        return False

    def play(self, alias, vol):
        self.cmd('setaudio %s volume to %d' % (alias, vol))
        self.cmd('play %s from 0' % alias)

    def stop(self, alias):
        self.cmd('stop %s' % alias)

    def close(self, alias):
        self.cmd('close %s' % alias)
        self.opened.discard(alias)

    def playing(self, alias):
        self.cmd('status %s mode' % alias)
        return self.buf.value == 'playing'

    def volume(self, alias, vol):
        self.cmd('setaudio %s volume to %d' % (alias, vol))


class Audio:
    """Procedural music + sfx.  Safe to use even if no audio device exists."""

    def __init__(self, mute=False):
        self.ok = False
        self.muted = mute
        self.mvol = 6
        self.svol = 8
        self.dir = CACHE_DIR
        self.win = None
        self.cmdline = None
        self.ready_sfx = set()
        self.loaded = set()
        self.last_play = {}
        self.sfx_n = 0
        self.want = None
        self.cur = None
        self.music_ready = {}
        self.music_proc = None
        self.tickn = 0
        self.gen_lock = threading.Lock()
        try:
            try:
                os.makedirs(self.dir, exist_ok=True)
                test = os.path.join(self.dir, '.w')
                open(test, 'w').close()
            except Exception:
                self.dir = tempfile.mkdtemp(prefix='tt_audio_')
            if sys.platform.startswith('win'):
                self.win = _WinBackend()
                self.ok = True
            elif sys.platform == 'darwin' and shutil.which('afplay'):
                self.cmdline = 'afplay'
                self.ok = True
            else:
                for c in ('paplay', 'aplay', 'ffplay'):
                    if shutil.which(c):
                        self.cmdline = c
                        self.ok = True
                        break
        except Exception:
            self.ok = False
        if self.ok:
            threading.Thread(target=self._render_sfx, daemon=True).start()

    # -- helpers ----------------------------------------------------------
    @staticmethod
    def gain(v):
        return (max(0, min(10, v)) / 10.0) ** 1.6

    def _render_sfx(self):
        for name, fn in SFX_DEFS.items():
            try:
                path = os.path.join(self.dir, 'sfx_%s.wav' % name)
                if not os.path.exists(path):
                    write_wav(path, fn())
                self.ready_sfx.add(name)
            except Exception:
                pass

    def _spawn(self, path, vol01):
        try:
            if self.cmdline == 'afplay':
                return subprocess.Popen(['afplay', '-v', '%.2f' % vol01, path],
                                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            if self.cmdline == 'paplay':
                return subprocess.Popen(['paplay', '--volume=%d' % int(vol01 * 65536), path],
                                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            if self.cmdline == 'aplay':
                return subprocess.Popen(['aplay', '-q', path],
                                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            if self.cmdline == 'ffplay':
                return subprocess.Popen(['ffplay', '-nodisp', '-autoexit', '-loglevel', 'quiet',
                                         '-volume', str(int(vol01 * 100)), path],
                                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        except Exception:
            return None
        return None

    # -- sfx ----------------------------------------------------------------
    def play(self, name):
        if not self.ok or self.muted or self.svol <= 0 or name not in self.ready_sfx:
            return
        now = time.perf_counter()
        if now - self.last_play.get(name, 0) < 0.05:
            return
        self.last_play[name] = now
        path = os.path.join(self.dir, 'sfx_%s.wav' % name)
        g = self.gain(self.svol)
        try:
            if self.win:
                self.sfx_n += 1
                alias = 'sfx%s%d' % (name, self.sfx_n % 3)
                if alias not in self.win.opened:
                    if not self.win.open(alias, path):
                        return
                self.win.play(alias, int(g * 1000))
            else:
                self._spawn(path, g)
        except Exception:
            pass

    # -- music --------------------------------------------------------------
    def music(self, key, seed, mood):
        if not self.ok or key == self.want:
            return
        self.want = key
        self.stop_music()
        path = os.path.join(self.dir, 'mus_%s_%d_v2.wav' % (mood, seed))
        if os.path.exists(path):
            self.music_ready[key] = path
            return

        def run():
            try:
                with self.gen_lock:
                    write_wav(path, gen_music(seed, mood))
                self.music_ready[key] = path
            except Exception:
                pass
        threading.Thread(target=run, daemon=True).start()

    def stop_music(self):
        try:
            if self.win and self.cur:
                self.win.stop('tt_music')
                self.win.close('tt_music')
            if self.music_proc:
                self.music_proc.terminate()
        except Exception:
            pass
        self.cur = None
        self.music_proc = None

    def set_volumes(self):
        try:
            if self.win and self.cur:
                self.win.volume('tt_music', int(self.gain(self.mvol) * 1000 * (0 if self.muted else 1)))
        except Exception:
            pass

    def tick(self):
        if not self.ok:
            return
        self.tickn += 1
        try:
            if self.want and self.cur != self.want and self.want in self.music_ready:
                path = self.music_ready[self.want]
                self.cur = self.want
                if self.win:
                    if self.win.open('tt_music', path):
                        self.win.play('tt_music', int(self.gain(self.mvol) * 1000 * (0 if self.muted else 1)))
                elif not self.muted and self.mvol > 0:
                    self.music_proc = self._spawn(path, self.gain(self.mvol) * 0.7)
            elif self.cur and self.tickn % 6 == 0:
                if self.win:
                    if not self.win.playing('tt_music'):
                        self.win.play('tt_music', int(self.gain(self.mvol) * 1000 * (0 if self.muted else 1)))
                elif (self.music_proc is None or self.music_proc.poll() is not None) \
                        and not self.muted and self.mvol > 0:
                    self.music_proc = self._spawn(self.music_ready[self.cur], self.gain(self.mvol) * 0.7)
        except Exception:
            pass

    def shutdown(self):
        try:
            self.stop_music()
            if self.win:
                for a in list(self.win.opened):
                    self.win.close(a)
        except Exception:
            pass


# ============================================================================
#  CUSTOM LEVELS  (.tttl)  -  one grid format shared by the editor, My Levels and story arenas
# ============================================================================
LEVELS_DIR = os.path.join(_HERE, 'levels')
MUSIC_DIR = os.path.join(_HERE, 'music')

try:
    os.makedirs(LEVELS_DIR, exist_ok=True)
    os.makedirs(MUSIC_DIR, exist_ok=True)
except Exception:
    pass
MUSIC_DIR = os.path.join(_HERE, 'music')
TTTL_HEAD = 'TTTL1'
MAX_W, MAX_H = 160, 120

# glyph, label
GLYPH_INFO = [
    ('#', 'BRICK'), ('c', 'CRUMBLE'), ('u', 'SPIKE UP'), ('d', 'SPIKE DOWN'),
    ('l', 'SPIKE LEFT'), ('r', 'SPIKE RIGHT'),
    ('^', 'GRAVITY UP'), ('v', 'GRAVITY DOWN'), ('<', 'GRAVITY LEFT'), ('>', 'GRAVITY RIGHT'),
    ('1', 'WIND UP'), ('2', 'WIND DOWN'), ('3', 'WIND LEFT'), ('4', 'WIND RIGHT'),
    ('5', 'UPDRAFT +RESET'), ('6', 'DOWNDRAFT +RESET'),
    ('S', 'SPRING'), ('o', 'SOUL'), ('C', 'CHECKPOINT'), ('W', 'WISP ORBIT'),
    ('H', 'SAW SIDEWAYS'), ('I', 'SAW UPDOWN'), ('P', 'PLAYER START'), ('D', 'GOAL DOOR'),
]
GLYPH_SET = set(g for g, _ in GLYPH_INFO) | {'.'}
GLYPH_LABEL = dict(GLYPH_INFO)


class GridLevel(Level):
    """A free-form level built from a data dict (see level_to_data / text_to_data)."""

    def __init__(self, data):
        self.data = data
        self.name = data.get('name', 'UNTITLED')
        self.sub = 'BY ' + str(data.get('author', 'UNKNOWN')).upper()
        self.theme = int(data.get('theme', 0)) % len(THEMES)
        self.inverted = bool(data.get('inv', False))
        self.par = int(data.get('par', 120))
        self.hints_on = True
        self.kind = 'grid'
        self.ents = []
        self.song = data.get('music')
        rows = data.get('rows') or ['.' * 10]
        self.H = len(rows)
        W = max(len(r) for r in rows)
        self.W = W
        self.ring = bool(data.get('ring', False))
        self.spec = dict(seed=sum(ord(ch) for ch in self.name) % 9973 + W, name=self.name,
                         rooms=['START', 'END'], theme=self.theme)
        self.build_grid(rows, data)

    def build_grid(self, rows, data):
        H, W = self.H, self.W
        self.R = H
        self.wpx, self.hpx = W * TILE, H * TILE
        g = [[0] * W for _ in range(H)]
        self.g = g
        self.crystals, self.springs, self.souls, self.cps = [], [], [], []
        self.orbits, self.saws, self.hints = [], [], []
        fm = {}
        cmap = {'^': UP, 'v': DOWN, '<': LEFT, '>': RIGHT}
        fmap = {'1': (UP, False), '2': (DOWN, False), '3': (LEFT, False), '4': (RIGHT, False),
                '5': (UP, True), '6': (DOWN, True)}
        smap = {'u': 2, 'd': 3, 'l': 4, 'r': 5}
        spawn = None
        self.door = None
        springs = []
        for r, row in enumerate(rows):
            for c, ch in enumerate(row.ljust(W, '.')):
                if ch == '.' or ch not in GLYPH_SET:
                    continue
                if ch == '#':
                    g[r][c] = 1
                elif ch == 'c':
                    g[r][c] = 6
                elif ch in smap:
                    g[r][c] = smap[ch]
                elif ch in cmap:
                    self.crystals.append(dict(c=c, r=r, d=cmap[ch]))
                elif ch in fmap:
                    fm[(r, c)] = fmap[ch]
                elif ch == 'o':
                    self.souls.append(dict(c=c, r=r))
                elif ch == 'S':
                    springs.append((r, c))
                elif ch == 'C':
                    self.cps.append(dict(c=c, r=r))
                elif ch == 'W':
                    self.orbits.append(dict(cx=c * TILE + 8, cy=r * TILE + 8, rx=2.4 * TILE, ry=1.8 * TILE,
                                            w=0.034 * (1 if (c + r) % 2 else -1),
                                            ph=((c * 7 + r * 13) % 628) / 100.0))
                elif ch in 'HI':
                    self.saws.append(dict(cx=c * TILE + 8, cy=r * TILE + 8, half=36, w=0.04 * (1 if (c + r) % 2 else -1),
                                          ph=((c * 5 + r * 11) % 628) / 100.0, axis='h' if ch == 'H' else 'v'))
                elif ch == 'P':
                    spawn = (c, r)
                elif ch == 'D':
                    self.door = (c * TILE, ((r + 1) * TILE - 32) if not self.inverted else r * TILE)
        self.fieldmap = fm
        sol = lambda rr, cc: 0 <= rr < H and 0 <= cc < W and g[rr][cc] in (1, 6)
        for (r, c) in springs:
            if sol(r + 1, c):
                d = UP
            elif sol(r - 1, c):
                d = DOWN
            elif sol(r, c - 1):
                d = RIGHT
            elif sol(r, c + 1):
                d = LEFT
            else:
                d = UP
            self.springs.append(dict(c=c, r=r, d=d))
        if spawn is None:
            spawn = (1, 1)
            for r in range(H - 2, 0, -1):
                found = False
                for c in range(W):
                    if g[r][c] == 0 and sol(r + 1, c):
                        spawn, found = (c, r), True
                        break
                if found:
                    break
        c, r = spawn
        self.spawn = (c * TILE + 2, (r * TILE if self.inverted else (r + 1) * TILE - PS))
        self.default_g = UP if self.inverted else DOWN
        for h in data.get('hints', []):
            try:
                self.hints.append(dict(x=int(h['c']) * TILE + 8, y=int(h['r']) * TILE,
                                       text=str(h['t']).upper()[:40], room=False))
            except Exception:
                pass
        self.bounds = [(0, H - 1)]
        self.finish()


def blank_data(name='UNTITLED', w=40, h=24, ring=False, theme=0, author='ME'):
    rows = [['.'] * w for _ in range(h)]
    for c in range(w):
        rows[0][c] = rows[1][c] = rows[h - 1][c] = rows[h - 2][c] = '#'
    if not ring:
        for r in range(h):
            rows[r][0] = rows[r][1] = rows[r][w - 1] = rows[r][w - 2] = '#'
    rows[h - 3][3] = 'P'
    rows[h - 3][w - 4] = 'D'
    return dict(fmt='TTTL', ver=1, name=name, author=author, theme=theme, inv=False, ring=ring,
                par=120, rows=[''.join(r) for r in rows], hints=[], music=None)


def clean_data(d):
    """validate / sanitise untrusted level data (imports)"""
    if not isinstance(d, dict) or d.get('fmt') != 'TTTL':
        raise ValueError('NOT A TTTL FILE')
    rows = d.get('rows')
    if not isinstance(rows, list) or not rows or len(rows) > MAX_H:
        raise ValueError('BAD SIZE')
    rows = [str(r)[:MAX_W] for r in rows]
    W = max(len(r) for r in rows)
    if W < 8 or len(rows) < 8:
        raise ValueError('LEVEL TOO SMALL')
    rows = [''.join(ch if ch in GLYPH_SET else '.' for ch in r.ljust(W, '.')) for r in rows]
    out = dict(fmt='TTTL', ver=1, rows=rows)
    out['name'] = str(d.get('name', 'UNTITLED')).upper()[:24]
    out['author'] = str(d.get('author', 'UNKNOWN')).upper()[:16]
    out['theme'] = int(d.get('theme', 0)) % len(THEMES)
    out['inv'] = bool(d.get('inv', False))
    out['ring'] = bool(d.get('ring', False))
    out['par'] = max(10, min(3600, int(d.get('par', 120))))
    hs = []
    for h in (d.get('hints') or [])[:60]:
        try:
            hs.append(dict(c=int(h['c']), r=int(h['r']), t=str(h['t']).upper()[:40]))
        except Exception:
            pass
    out['hints'] = hs
    m = d.get('music')
    out['music'] = clean_song(m) if m else None
    return out


def data_to_text(d):
    return TTTL_HEAD + '\n' + json.dumps(d, separators=(',', ':'))


def text_to_data(txt):
    txt = txt.lstrip('\ufeff')
    if not txt.startswith('TTTL'):
        raise ValueError('NOT A TTTL FILE')
    body = txt.split('\n', 1)[1] if '\n' in txt else ''
    return clean_data(json.loads(body))


def level_to_data(lvl, name=None, author='THE TOWER'):
    """convert any built Level (tower or grid) into editable data"""
    H, W = lvl.R, lvl.W
    rows = [['.'] * W for _ in range(H)]
    inv = {2: 'u', 3: 'd', 4: 'l', 5: 'r', 1: '#', 6: 'c'}
    for r in range(H):
        for c in range(W):
            v = lvl.g[r][c]
            if v:
                rows[r][c] = inv[v]
    for (r, c), (d, rs) in lvl.fieldmap.items():
        if 0 <= r < H and 0 <= c < W and rows[r][c] == '.':
            rows[r][c] = ('5' if d == UP else '6') if rs else '1234'[{UP: 0, DOWN: 1, LEFT: 2, RIGHT: 3}[d]]
    cm = {UP: '^', DOWN: 'v', LEFT: '<', RIGHT: '>'}
    for cr in lvl.crystals:
        rows[cr['r']][cr['c']] = cm[cr['d']]
    for s in lvl.springs:
        rows[s['r']][s['c']] = 'S'
    for s in lvl.souls:
        rows[s['r']][s['c']] = 'o'
    for s in lvl.cps:
        rows[s['r']][s['c']] = 'C'
    for o in lvl.orbits:
        rows[int(o['cy'] // TILE)][int(o['cx'] // TILE) % W] = 'W'
    for o in lvl.saws:
        rows[int(o['cy'] // TILE)][int(o['cx'] // TILE) % W] = 'H' if o.get('axis') != 'v' else 'I'
    sx, sy = lvl.spawn
    rows[min(H - 1, int((sy + (0 if lvl.inverted else PS - 1)) // TILE))][int((sx + PS / 2) // TILE) % W] = 'P'
    if lvl.door:
        dx, dy = lvl.door
        rows[min(H - 1, int((dy + (0 if lvl.inverted else 31)) // TILE))][int(dx // TILE) % W] = 'D'
    hints = [dict(c=int(h['x'] // TILE), r=int(h['y'] // TILE), t=h['text']) for h in lvl.hints][:60]
    return dict(fmt='TTTL', ver=1, name=(name or lvl.name).upper()[:24], author=author, theme=lvl.theme,
                inv=lvl.inverted, ring=lvl.ring, par=lvl.par, rows=[''.join(r) for r in rows],
                hints=hints, music=None)


def list_files(folder, ext):
    try:
        os.makedirs(folder, exist_ok=True)
        return sorted(f for f in os.listdir(folder) if f.lower().endswith(ext))
    except Exception:
        return []


def safe_name(s):
    return ''.join(ch if (ch.isalnum() or ch in '-_ ') else '_' for ch in s).strip()[:32] or 'untitled'


# ============================================================================
#  SONGS  (music maker format + renderer + generator)
# ============================================================================
SONG_SCALES = ['minor', 'dorian', 'phrygian', 'harmonic', 'major', 'pentatonic']
SCALES['major'] = [0, 2, 4, 5, 7, 9, 11]
SCALES['pentatonic'] = [0, 3, 5, 7, 10, 12, 15]
CH_NAMES = ['lead', 'arp', 'bass', 'drum']
CH_ROWS = {'lead': 15, 'arp': 15, 'bass': 10, 'drum': 5}
CH_BASE = {'lead': 24, 'arp': 12, 'bass': 0}
DRUM_NAMES = ['KICK', 'SNARE', 'HAT', 'OPEN', 'TOM']
NOTE_NAMES = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B']
WAVES = ['sq', 'tri', 'saw', 'sin']


def new_song(name='MY SONG'):
    pats = [dict(lead=[], arp=[], bass=[], drum=[]) for _ in range(4)]
    return dict(name=name, bpm=100, root=36, scale='minor', steps=32, pats=pats, order=[0],
                ch=dict(lead=dict(wave='sq', duty=0.25, vol=7), arp=dict(wave='sq', duty=0.125, vol=4),
                        bass=dict(wave='tri', duty=0.5, vol=8), drum=dict(wave='sq', duty=0.5, vol=7)))


def clean_song(s):
    try:
        out = new_song(str(s.get('name', 'SONG')).upper()[:20])
        out['bpm'] = max(50, min(220, int(s.get('bpm', 100))))
        out['root'] = max(24, min(48, int(s.get('root', 36))))
        out['scale'] = s.get('scale') if s.get('scale') in SONG_SCALES else 'minor'
        out['steps'] = 16 if int(s.get('steps', 32)) == 16 else 32
        pats = []
        for p in (s.get('pats') or [])[:16]:
            q = {}
            for ch in CH_NAMES:
                notes = []
                for n in (p.get(ch) or [])[:400]:
                    st, row, ln = int(n[0]), int(n[1]), int(n[2]) if len(n) > 2 else 1
                    if 0 <= st < out['steps'] and 0 <= row < CH_ROWS[ch]:
                        notes.append([st, row, max(1, min(out['steps'] - st, ln))])
                q[ch] = notes
            pats.append(q)
        out['pats'] = pats or out['pats']
        out['order'] = [int(i) for i in (s.get('order') or [0])[:64] if 0 <= int(i) < len(out['pats'])] or [0]
        for ch in CH_NAMES:
            c = (s.get('ch') or {}).get(ch) or {}
            out['ch'][ch] = dict(wave=c.get('wave') if c.get('wave') in WAVES else out['ch'][ch]['wave'],
                                 duty=float(c.get('duty', out['ch'][ch]['duty'])),
                                 vol=max(0, min(10, int(c.get('vol', out['ch'][ch]['vol'])))))
        return out
    except Exception:
        return new_song()


def song_pitch(song, ch, row):
    sc = SCALES[song['scale']]
    return song['root'] + CH_BASE[ch] + sc[row % 7] + 12 * (row // 7)


def render_song(song, order=None, pattern=None):
    """song -> array('h').  pattern=i renders just that pattern (looped twice)."""
    steps = song['steps']
    spn = int(60.0 / song['bpm'] / 4.0 * SR)
    seq = [pattern, pattern] if pattern is not None else (order or song['order'])
    total = spn * steps * len(seq)
    buf = [0] * total
    for bi, pi in enumerate(seq):
        pat = song['pats'][pi]
        base = bi * steps * spn
        for ch in ('bass', 'arp', 'lead'):
            cfg = song['ch'][ch]
            if cfg['vol'] <= 0:
                continue
            vol = cfg['vol'] * (700 if ch == 'bass' else 330)
            for (st, row, ln) in pat[ch]:
                f = midi_hz(song_pitch(song, ch, row))
                n = int(spn * ln * (0.96 if ch != 'arp' else 1.2))
                w = note_wave(cfg['wave'], f, n, vol, duty=cfg['duty'],
                              vib=0.004 if (ch == 'lead' and ln >= 3) else 0.0,
                              dec=1.2 if ch == 'bass' else (2.2 if ch == 'arp' else 1.0))
                mix_into(buf, w, base + st * spn)
        dv = song['ch']['drum']['vol'] / 7.0
        if dv > 0:
            for (st, row, ln) in pat['drum']:
                off = base + st * spn
                if row == 0:
                    mix_into(buf, kick_wave(int(spn * 2.2), 7000 * dv), off)
                elif row == 1:
                    mix_into(buf, noise_wave(int(spn * 2.4), 3400 * dv, 2.5, 3, 11 + st), off)
                elif row == 2:
                    mix_into(buf, noise_wave(int(spn * 0.8), 1500 * dv, 4.0, 1, 99), off)
                elif row == 3:
                    mix_into(buf, noise_wave(int(spn * 2.5), 1400 * dv, 1.5, 1, 77), off)
                else:
                    mix_into(buf, kick_wave(int(spn * 1.6), 5200 * dv), off)
        time.sleep(0.001)
    return array.array('h', [max(-30000, min(30000, v)) for v in buf])


def generate_song(seed, mood='foyer'):
    """structured random song for the maker's RANDOMISE button (same recipe as the game music)"""
    P = MOODS.get(mood, MOODS['foyer'])
    rnd = random.Random(seed * 17 + 5)
    song = new_song('GENERATED %d' % (seed % 1000))
    song['bpm'] = rnd.randrange(P['bpm'][0], P['bpm'][1] + 1, 2)
    song['scale'] = rnd.choice([s for s in P['scales'] if s in SONG_SCALES])
    song['root'] = 36 + rnd.randrange(0, 8)
    song['steps'] = 16
    progA = rnd.choice(PROGS)
    progB = rnd.choice([p for p in PROGS if p != progA])
    bass_pat = rnd.choice(BASS_PATS)
    arp_pat = rnd.choice(ARPS)
    rh = rnd.choice(RHYTHMS)

    def make_motif():
        deg, out = rnd.choice([0, 2, 4]) + 7, []
        for (s, ln) in rh:
            out.append((s, ln, deg))
            deg = max(4, min(14, deg + rnd.choices([-2, -1, 0, 1, 2], weights=[2, 3, 1, 3, 2])[0]))
        return out
    mA, mB = make_motif(), make_motif()
    pats = []
    order = []

    def bar(prog, bi, sec):
        deg = prog[bi % 4]
        p = dict(lead=[], arp=[], bass=[], drum=[])
        for s in range(16):
            if bass_pat[s] == 'x':
                p['bass'].append([s, deg % 7 + (7 if (s % 8 in (3, 6) and sec != 'A' and deg % 7 < 3) else 0), 3 if s % 4 == 0 else 2])
        ch = [deg, deg + 2, deg + 4, deg + 7]
        for s in range(16):
            if sec == 'A' and s % 2:
                continue
            p['arp'].append([s, min(14, ch[arp_pat[s % 4] % 4] + 7), 1])
        if sec != 'A':
            motif, shift = (mB if sec == 'B' else mA), ([0, 1, 0, -1] if sec != 'B' else [0, 2, 1, 0])[bi % 4]
            for k, (s, ln, dg) in enumerate(motif):
                d = dg + shift
                if s == 0 or k == len(motif) - 1:
                    d = min([deg, deg + 2, deg + 4, deg + 7], key=lambda t: abs(t - d - 0)) + 7 - 7
                    d = max(0, min(14, d + 7))
                p['lead'].append([s, max(0, min(14, d)), ln])
        for s in range(16):
            if s in (0, 8) or (s == 10 and sec in ('A3', 'B')):
                p['drum'].append([s, 0, 1])
            if s in (4, 12) and sec != 'A':
                p['drum'].append([s, 1, 1])
            if s % 2 == 0 and not (sec == 'A' and s % 4):
                p['drum'].append([s, 2, 1])
        return p
    for sec, prog in (('A', progA), ('A2', progA), ('B', progB), ('A3', progA)):
        for bi in range(4):
            pats.append(bar(prog, bi, sec))
            order.append(len(pats) - 1)
    song['pats'], song['order'] = pats[:16], order[:16]
    # (16 distinct patterns max: bars 0-15)
    return clean_song(song)


# ============================================================================
#  LEVEL EDITOR
# ============================================================================
PAL_SLOTS = [g for g, _ in GLYPH_INFO] + ['@HINT', '@ERASE', '@RECT']
SPIKE_GL = {'u': UP, 'd': DOWN, 'l': LEFT, 'r': RIGHT}
CRY_GL = {'^': UP, 'v': DOWN, '<': LEFT, '>': RIGHT}
FLD_GL = {'1': UP, '2': DOWN, '3': LEFT, '4': RIGHT, '5': UP, '6': DOWN}


def find_route(lvl, max_nodes=80000, hold=5, progress=None, cancel=None):
    """goal-directed (weighted A*) search over the real physics: can the player get from the start
    to the door?  (ignores wisps, saws and crumble timing)"""
    if not lvl.door:
        return None, 0
    import heapq
    sim = Sim(lvl, bot=True)
    dx, dy = lvl.door[0] + 8, lvl.door[1] + 16
    acts = [(m, j) for m in (-1, 0, 1) for j in (0, 1, 2)]

    def key(s):
        return (int(s[0] // 3), int(s[1] // 3), int(s[2] * 1.5), int(s[3] * 1.5), s[4], s[5], s[6], s[7] > 0, s[11])

    def heur(s):
        return (abs(lvl.wd(dx - (s[0] + PS / 2.0))) + abs(dy - (s[1] + PS / 2.0))) / 9.0
    s0 = sim.snap()
    heap = [(heur(s0) * 2.5, 0, 0, s0)]
    seen = {key(s0)}
    n = 0
    cnt = 0
    while heap and n < max_nodes:
        if cancel and cancel():
            return None, n
        _, _, depth, s = heapq.heappop(heap)
        n += 1
        if progress and n % 500 == 0:
            progress(n)
        for (m, j) in acts:
            sim.restore(s)
            ok = True
            for f in range(hold):
                sim.step(m, j > 0 and f == 0, (j == 2) or (j == 1 and f < 2))
                if sim.dead:
                    ok = False
                    break
                if abs(lvl.wd(dx - (sim.x + PS / 2.0))) < 7 and abs(dy - (sim.y + PS / 2.0)) < 14:
                    return True, n
            if not ok:
                continue
            ns = sim.snap()
            k = key(ns)
            if k not in seen:
                seen.add(k)
                cnt += 1
                heapq.heappush(heap, (depth + 1 + heur(ns) * 2.5, cnt, depth + 1, ns))
    return False, n


class Editor:
    TOP = 14
    BOT = 10

    def __init__(self, game, data=None, path=None):
        self.g = game
        d = data or blank_data()
        self.set_data(d)
        self.path = path
        self.tool = '#'
        self.rect_mode = False
        self.grid = True
        self.camx = self.W * TILE / 2.0
        self.camy = self.H * TILE / 2.0
        self.undo, self.redo = [], []
        self.dirty_lvl = True
        self.lvl = None
        self.rebuild_t = 0
        self.stroke = False
        self.last_cell = None
        self.rect_start = None
        self.edit = None
        self.msg = ('', 0)
        self.modal = None            # 'props' | 'open' | None
        self.mi = 0
        self.files = []
        self.saved_hash = self.hash()
        self.route = None
        self.route_thread = None
        self.route_prog = 0
        self.pan_drag = None
        self.rebuild()

    # -- data ---------------------------------------------------------------
    def set_data(self, d):
        self.name, self.author = d.get('name', 'UNTITLED'), d.get('author', 'ME')
        self.theme, self.inv, self.ring = d.get('theme', 0), d.get('inv', False), d.get('ring', False)
        self.par = d.get('par', 120)
        self.cells = [list(r) for r in d['rows']]
        self.H, self.W = len(self.cells), len(self.cells[0])
        self.hints = [dict(h) for h in d.get('hints', [])]
        self.music = d.get('music')

    def to_data(self):
        return dict(fmt='TTTL', ver=1, name=self.name, author=self.author, theme=self.theme, inv=self.inv,
                    ring=self.ring, par=self.par, rows=[''.join(r) for r in self.cells],
                    hints=[dict(h) for h in self.hints], music=self.music)

    def hash(self):
        return json.dumps(self.to_data(), sort_keys=True)

    def rebuild(self):
        try:
            self.lvl = GridLevel(self.to_data())
        except Exception as e:
            self.say('BUILD ERROR')
        self.dirty_lvl = False

    def say(self, s, n=150):
        self.msg = (s, n)

    def push_undo(self):
        self.undo.append((json.dumps([''.join(r) for r in self.cells]), json.dumps(self.hints)))
        if len(self.undo) > 60:
            self.undo.pop(0)
        self.redo = []

    def apply_snap(self, snap):
        self.cells = [list(r) for r in json.loads(snap[0])]
        self.hints = json.loads(snap[1])
        self.H, self.W = len(self.cells), len(self.cells[0])
        self.dirty_lvl = True

    def do_undo(self):
        if self.undo:
            self.redo.append((json.dumps([''.join(r) for r in self.cells]), json.dumps(self.hints)))
            self.apply_snap(self.undo.pop())
            self.say('UNDO')

    def do_redo(self):
        if self.redo:
            self.undo.append((json.dumps([''.join(r) for r in self.cells]), json.dumps(self.hints)))
            self.apply_snap(self.redo.pop())
            self.say('REDO')

    # -- geometry -----------------------------------------------------------
    def cell_at(self, mx, my):
        wx = self.camx + (mx - self.g.VW / 2.0)
        wy = self.camy + (my - self.g.VH / 2.0)
        c, r = int(wx // TILE), int(wy // TILE)
        if self.ring:
            c %= self.W
        return c, r

    def in_map(self, c, r):
        return 0 <= r < self.H and 0 <= c < self.W

    def over_ui(self, mx, my):
        return my < self.TOP or my > self.g.VH - self.BOT or mx > self.g.VW - 52

    def set_cell(self, c, r, ch):
        if not self.in_map(c, r) or self.cells[r][c] == ch:
            return
        if ch in 'PD':
            for rr in range(self.H):
                for cc in range(self.W):
                    if self.cells[rr][cc] == ch:
                        self.cells[rr][cc] = '.'
        self.cells[r][c] = ch
        self.dirty_lvl = True

    def line(self, a, b):
        (c0, r0), (c1, r1) = a, b
        n = max(abs(c1 - c0), abs(r1 - r0), 1)
        return [(round(c0 + (c1 - c0) * i / n), round(r0 + (r1 - r0) * i / n)) for i in range(n + 1)]

    # -- file ops -------------------------------------------------------------
    def save(self, path=None):
        try:
            os.makedirs(LEVELS_DIR, exist_ok=True)
            p = path or self.path or os.path.join(LEVELS_DIR, safe_name(self.name) + '.tttl')
            with open(p, 'w', encoding='utf-8') as f:
                f.write(data_to_text(self.to_data()))
            self.path = p
            self.saved_hash = self.hash()
            self.say('SAVED ' + os.path.basename(p).upper())
            self.g.sfx('ok')
            return True
        except Exception as e:
            self.say('SAVE FAILED')
            return False

    def export_as(self):
        try:
            os.makedirs(LEVELS_DIR, exist_ok=True)
            p = export_target(safe_name(self.name) + '.tttl')
            if p:
                with open(p, 'w', encoding='utf-8') as f:
                    f.write(data_to_text(self.to_data()))
                self.say('EXPORTED')
        except Exception:
            self.say('EXPORT FAILED - USE SAVE')

    def import_file(self):
        try:
            self.g.pick_file(('.tttl',), lambda p: self.load_path(p, copy=True), 'IMPORT LEVEL')
        except Exception:
            self.say('IMPORT FAILED - COPY FILE TO LEVELS FOLDER')

    def load_path(self, p, copy=False):
        try:
            with open(p, 'r', encoding='utf-8') as f:
                d = text_to_data(f.read())
            self.push_undo()
            self.set_data(d)
            self.path = p
            if copy:
                os.makedirs(LEVELS_DIR, exist_ok=True)
                self.path = os.path.join(LEVELS_DIR, safe_name(self.name) + '.tttl')
                with open(self.path, 'w', encoding='utf-8') as f:
                    f.write(data_to_text(d))
            self.saved_hash = self.hash()
            self.dirty_lvl = True
            self.say('LOADED ' + self.name)
        except Exception as e:
            self.say('LOAD FAILED: ' + str(e)[:24].upper())

    def new_level(self):
        self.push_undo()
        self.set_data(blank_data(theme=self.theme))
        self.path = None
        self.camx, self.camy = self.W * TILE / 2.0, self.H * TILE / 2.0
        self.dirty_lvl = True
        self.say('NEW LEVEL')

    def start_route(self):
        if self.route_thread and self.route_thread.is_alive():
            return
        if self.dirty_lvl:
            self.rebuild()
        lvl = self.lvl
        self.route = ('...', 0)
        self.route_prog = 0

        def run():
            def prog(n):
                self.route_prog = n
            try:
                ok, n = find_route(lvl, 80000, progress=prog)
                if ok is None:
                    self.route = ('NO GOAL DOOR PLACED' if not lvl.door else 'CANCELLED', n)
                elif ok:
                    self.route = ('ROUTE FOUND - BEATABLE', n)
                else:
                    self.route = ('NO ROUTE IN %d STATES (MAYBE STILL POSSIBLE)' % n, n)
            except Exception:
                self.route = ('CHECK FAILED', 0)
        self.route_thread = threading.Thread(target=run, daemon=True)
        self.route_thread.start()

    # -- text entry -----------------------------------------------------------
    def begin_text(self, label, initial, cb, maxlen=30):
        self.edit = dict(label=label, buf=initial, cb=cb, maxlen=maxlen)
        self.g.chars = []

    def upd_text(self):
        g = self.g
        e = self.edit
        for ch in g.chars:
            if len(e['buf']) < e['maxlen']:
                e['buf'] += ch.upper()
        g.chars = []
        if 'backspace' in g.events:
            e['buf'] = e['buf'][:-1]
        if 'return' in g.events or 'kp_enter' in g.events:
            cb = e['cb']
            buf = e['buf']
            self.edit = None
            cb(buf)
        elif 'escape' in g.events:
            self.edit = None

    # -- update ---------------------------------------------------------------

    def update(self):
        g = self.g
        if self.msg[1] > 0:
            self.msg = (self.msg[0], self.msg[1] - 1)
        self.rebuild_t += 1
        if self.dirty_lvl and (self.rebuild_t % 8 == 0 or not self.stroke):
            self.rebuild()
        if self.edit:
            self.upd_text()
            g.mev = []
            return
        if self.modal:
            self.upd_modal()
            g.mev = []
            return
        ctrl = bool(g.held & {'control_l', 'control_r'})
        shift = bool(g.held & {'shift_l', 'shift_r'})
        ev = g.events
        if ctrl and 'z' in ev:
            self.do_undo()
        elif ctrl and 'y' in ev:
            self.do_redo()
        elif ctrl and 's' in ev:
            self.save()
        elif ctrl and 'o' in ev:
            self.open_modal('open')
        elif ctrl and 'n' in ev:
            self.new_level()
        elif 'f5' in ev:
            self.playtest()
        elif 'g' in ev and not ctrl:
            self.grid = not self.grid
        elif 'q' in ev:
            self.tool = PAL_SLOTS[(PAL_SLOTS.index(self.tool) - 1) % len(PAL_SLOTS)]
        elif 'e' in ev:
            self.tool = PAL_SLOTS[(PAL_SLOTS.index(self.tool) + 1) % len(PAL_SLOTS)]
        elif 'f2' in ev:
            self.open_modal('props')
        elif 'escape' in ev:
            self.leave()
            return
        # pan
        sp = 8 if shift else 3
        dx = (1 if g.held & {'right', 'd'} else 0) - (1 if g.held & {'left', 'a'} else 0)
        dy = (1 if g.held & {'down', 's'} else 0) - (1 if g.held & {'up', 'w'} else 0)
        if ctrl:
            dx = dy = 0
        self.camx += dx * sp
        self.camy += dy * sp
        # mouse
        for (kind, btn, x, y) in g.mev:
            if kind == 'wheel':
                self.tool = PAL_SLOTS[(PAL_SLOTS.index(self.tool) + btn) % len(PAL_SLOTS)]
            elif kind == 'down':
                self.mouse_down(btn, x, y, shift)
            elif kind == 'up':
                self.mouse_up(btn, x, y)
        g.mev = []
        if self.pan_drag and 2 in g.mdown:
            ox, oy, cx0, cy0 = self.pan_drag
            self.camx = cx0 - (g.mx - ox)
            self.camy = cy0 - (g.my - oy)
        elif self.pan_drag:
            self.pan_drag = None
        if self.stroke and not self.over_ui(g.mx, g.my):
            cell = self.cell_at(g.mx, g.my)
            if self.rect_start is None and cell != self.last_cell:
                for (c, r) in self.line(self.last_cell or cell, cell):
                    if self.ring:
                        c %= self.W
                    self.apply_tool(c, r, 3 in g.mdown or self.stroke_btn == 3)
                self.last_cell = cell
        if not self.ring:
            self.camx = max(0, min(self.W * TILE, self.camx))
        self.camy = max(0, min(self.H * TILE, self.camy))

    def apply_tool(self, c, r, erase):
        if erase or self.tool == '@ERASE':
            self.set_cell(c, r, '.')
        elif self.tool in ('@HINT', '@RECT'):
            pass
        else:
            self.set_cell(c, r, self.tool)

    def mouse_down(self, btn, x, y, shift):
        g = self.g
        if y < self.TOP:
            self.top_click(x)
            return
        if x > g.VW - 52:
            self.palette_click(x, y)
            return
        if y > g.VH - self.BOT:
            return
        c, r = self.cell_at(x, y)
        if btn == 2:
            self.pan_drag = (x, y, self.camx, self.camy)
            return
        if not self.in_map(c, r):
            return
        if self.tool == '@HINT' and btn == 1:
            ex = [h for h in self.hints if h['c'] == c and h['r'] == r]
            self.begin_text('SIGN TEXT', ex[0]['t'] if ex else '', lambda s, c=c, r=r: self.set_hint(c, r, s), 40)
            return
        if btn == 3:
            ex = [h for h in self.hints if h['c'] == c and h['r'] == r]
            if ex:
                self.push_undo()
                self.hints.remove(ex[0])
                self.dirty_lvl = True
                return
        self.push_undo()
        self.stroke = True
        self.stroke_btn = btn
        self.last_cell = (c, r)
        if (self.rect_mode or shift) and btn == 1:
            self.rect_start = (c, r)
        else:
            self.rect_start = None
            self.apply_tool(c, r, btn == 3)

    def mouse_up(self, btn, x, y):
        if self.stroke and self.rect_start:
            c, r = self.cell_at(x, y)
            c0, r0 = self.rect_start
            for rr in range(min(r0, r), max(r0, r) + 1):
                for cc in range(min(c0, c), max(c0, c) + 1):
                    self.apply_tool(cc, rr, False)
        self.stroke = False
        self.rect_start = None
        self.pan_drag = None if btn == 2 else self.pan_drag

    def set_hint(self, c, r, s):
        self.push_undo()
        self.hints = [h for h in self.hints if not (h['c'] == c and h['r'] == r)]
        if s.strip():
            self.hints.append(dict(c=c, r=r, t=s.strip()))
        self.dirty_lvl = True

    def palette_click(self, x, y):
        col = int((x - (self.g.VW - 50)) // 16)
        row = int((y - 16) // 16)
        if 0 <= col < 3 and 0 <= row < 9:
            i = row * 3 + col
            if i < len(PAL_SLOTS):
                t = PAL_SLOTS[i]
                if t == '@RECT':
                    self.rect_mode = not self.rect_mode
                else:
                    self.tool = t

    TOP_BTNS = [('NEW', 'new'), ('OPEN', 'open'), ('SAVE', 'save'), ('EXPORT', 'export'),
                ('IMPORT', 'import'), ('PLAY', 'play'), ('CHECK', 'check'), ('SETUP', 'props'),
                ('UNDO', 'undo'), ('GRID', 'grid'), ('EXIT', 'exit')]

    def top_layout(self):
        x, out = 3, []
        for label, act in self.TOP_BTNS:
            w = len(label) * 4 + 4
            out.append((x, w, label, act))
            x += w + 2
        return out

    def top_click(self, mx):
        for (x, w, label, act) in self.top_layout():
            if x <= mx <= x + w:
                {'new': self.new_level, 'open': lambda: self.open_modal('open'), 'save': self.save,
                 'export': self.export_as, 'import': self.import_file, 'play': self.playtest,
                 'check': self.start_route, 'props': lambda: self.open_modal('props'),
                 'undo': self.do_undo, 'grid': lambda: setattr(self, 'grid', not self.grid),
                 'exit': self.leave}[act]()
                return

    def leave(self):
        if self.hash() != self.saved_hash:
            self.save()
        self.g.leave_editor()

    def playtest(self):
        self.rebuild()
        if not self.lvl.door:
            self.say('PLACE A GOAL DOOR FIRST')
            return
        self.g.start_test(self)

    # -- modals ---------------------------------------------------------------
    def open_modal(self, kind):
        self.modal = kind
        self.mi = 0
        if kind == 'open':
            self.files = list_files(LEVELS_DIR, '.tttl')
        self.g.mev = []

    PROP_ROWS = ['NAME', 'AUTHOR', 'WORLD', 'GRAVITY', 'EDGES', 'PAR TIME', 'WIDTH', 'HEIGHT',
                 'BORDER WALLS', 'MUSIC', 'CLOSE']

    def upd_modal(self):
        g = self.g
        ev = g.events
        if 'escape' in ev:
            self.modal = None
            return
        if self.modal == 'open':
            n = len(self.files)
            if 'c' in ev:
                self.camp_i = (getattr(self, 'camp_i', -1) + 1) % len(LEVELS)
                self.push_undo()
                self.set_data(level_to_data(Level(LEVELS[self.camp_i])))
                self.path = None
                self.modal = None
                self.dirty_lvl = True
                self.camx, self.camy = self.W * TILE / 2.0, self.H * TILE / 2.0
                self.say('REMIX: ' + self.name)
                return
            if n:
                if 'up' in ev or 'w' in ev:
                    self.mi = (self.mi - 1) % n
                if 'down' in ev or 's' in ev:
                    self.mi = (self.mi + 1) % n
                if 'return' in ev:
                    self.load_path(os.path.join(LEVELS_DIR, self.files[self.mi]))
                    self.modal = None
                if 'delete' in ev:
                    try:
                        os.remove(os.path.join(LEVELS_DIR, self.files[self.mi]))
                        self.files = list_files(LEVELS_DIR, '.tttl')
                        self.mi = 0
                    except Exception:
                        pass
            return
        n = len(self.PROP_ROWS)
        if 'up' in ev or 'w' in ev:
            self.mi = (self.mi - 1) % n
        if 'down' in ev or 's' in ev:
            self.mi = (self.mi + 1) % n
        step = (1 if ('right' in ev or 'd' in ev) else 0) - (1 if ('left' in ev or 'a' in ev) else 0)
        ok = 'return' in ev
        row = self.PROP_ROWS[self.mi]
        if row == 'NAME' and ok:
            self.begin_text('LEVEL NAME', self.name, lambda s: setattr(self, 'name', s.strip() or 'UNTITLED'), 24)
        elif row == 'AUTHOR' and ok:
            self.begin_text('AUTHOR', self.author, lambda s: setattr(self, 'author', s.strip() or 'ME'), 16)
        elif row == 'WORLD' and (step or ok):
            self.theme = (self.theme + (step or 1)) % len(THEMES)
            self.dirty_lvl = True
        elif row == 'GRAVITY' and (step or ok):
            self.inv = not self.inv
            self.dirty_lvl = True
        elif row == 'EDGES' and (step or ok):
            self.ring = not self.ring
            self.dirty_lvl = True
        elif row == 'PAR TIME' and (step or ok):
            self.par = max(10, min(3600, self.par + 10 * (step or 1)))
        elif row in ('WIDTH', 'HEIGHT') and step:
            self.push_undo()
            self.resize(step if row == 'WIDTH' else 0, step if row == 'HEIGHT' else 0)
        elif row == 'BORDER WALLS' and ok:
            self.push_undo()
            for r in range(self.H):
                for c in range(self.W):
                    if r < 2 or r >= self.H - 2 or (not self.ring and (c < 2 or c >= self.W - 2)):
                        self.cells[r][c] = '#'
            self.dirty_lvl = True
            self.say('BORDER BUILT')
        elif row == 'MUSIC' and (step or ok):
            names = [None] + list_files(MUSIC_DIR, '.tttm')
            cur = self.music_name if hasattr(self, 'music_name') else None
            i = (names.index(cur) if cur in names else 0)
            i = (i + (step or 1)) % len(names)
            self.music_name = names[i]
            if names[i] is None:
                self.music = None
            else:
                try:
                    with open(os.path.join(MUSIC_DIR, names[i]), 'r', encoding='utf-8') as f:
                        self.music = clean_song(json.loads(f.read().split('\n', 1)[1]))
                except Exception:
                    self.music = None
                    self.say('BAD SONG FILE')
        elif row == 'CLOSE' and ok:
            self.modal = None

    def resize(self, dw, dh):
        if dw:
            nw = max(10, min(MAX_W, self.W + dw * (4 if self.g.held & {'shift_l', 'shift_r'} else 1)))
            for r in range(self.H):
                row = self.cells[r]
                row[:] = row[:nw] + ['.'] * (nw - len(row))
            self.W = nw
        if dh:
            nh = max(10, min(MAX_H, self.H + dh * (4 if self.g.held & {'shift_l', 'shift_r'} else 1)))
            if nh > self.H:
                self.cells += [['.'] * self.W for _ in range(nh - self.H)]
            else:
                self.cells = self.cells[:nh]
            self.H = nh
        self.dirty_lvl = True

    # -- drawing --------------------------------------------------------------
    def glyph_image(self, ch):
        A, th, t = self.g.assets, self.theme, self.g.t
        if ch == '#':
            return A.brick(th, 0, True, True, False, 0)
        if ch == 'c':
            return A.crumble(th, 0)
        if ch in SPIKE_GL:
            return A.spike(SPIKE_GL[ch])
        if ch in CRY_GL:
            return A.crystal(CRY_GL[ch], (t // 10) % 2)
        if ch in FLD_GL:
            return A.field(th, FLD_GL[ch], (t // 4) % 4)
        return {'S': lambda: A.spring(UP, 0), 'o': lambda: A.orb((t // 12) % 2),
                'C': lambda: A.brazier(th, True, t // 6),
                'W': lambda: A.wisp((t // 5) % 2), 'H': lambda: A.saw((t // 2) % 4),
                'I': lambda: A.saw((t // 2) % 4),
                'P': lambda: A.player('stand', 1, UP if self.inv else DOWN, self.g.save['opts']['skin']),
                'D': lambda: A.door_icon(th)}.get(ch, lambda: None)()

    def draw(self):
        g = self.g
        VW, VH = g.VW, g.VH
        if self.lvl is None:
            return
        g.draw_scene(self.lvl, None, self.camx, self.camy, edit=True)
        sx = lambda wx: wx - self.camx + VW / 2.0
        sy = lambda wy: wy - self.camy + VH / 2.0
        # map bounds
        g.rect(sx(-1), sy(-1), self.W * TILE + 2, 1, '#ff6ad5')
        g.rect(sx(-1), sy(self.H * TILE), self.W * TILE + 2, 1, '#ff6ad5')
        g.rect(sx(-1), sy(0), 1, self.H * TILE, '#ff6ad5')
        g.rect(sx(self.W * TILE), sy(0), 1, self.H * TILE, '#ff6ad5')
        if self.grid:
            c0 = int((self.camx - VW / 2.0) // TILE)
            c1 = int((self.camx + VW / 2.0) // TILE) + 1
            r0 = int((self.camy - VH / 2.0) // TILE)
            r1 = int((self.camy + VH / 2.0) // TILE) + 1
            for c in range(c0, c1 + 1):
                if 0 <= c <= self.W or self.ring:
                    g.rect(sx(c * TILE), self.TOP, 1, VH - self.TOP - self.BOT, '#241f4a')
            for r in range(max(0, r0), min(self.H, r1) + 1):
                g.rect(0, sy(r * TILE), VW - 52, 1, '#241f4a')
        # spawn / hints
        for h in self.hints:
            x, y = sx(h['c'] * TILE + 8), sy(h['r'] * TILE)
            g.rect(x - 2, y + 4, 4, 4, C_GOLD)
            g.text(h['t'], x, y - 6, C_TEXT, 1, 'c')
        # cursor
        mx, my = g.mx, g.my
        if not self.over_ui(mx, my) and not self.modal and not self.edit:
            c, r = self.cell_at(mx, my)
            x, y = sx(c * TILE), sy(r * TILE)
            if self.rect_start:
                c0, r0 = self.rect_start
                a, b = min(c0, c), min(r0, r)
                w, h = abs(c - c0) + 1, abs(r - r0) + 1
                x, y, ww, hh = sx(a * TILE), sy(b * TILE), w * TILE, h * TILE
                for (rx, ry, rw, rh) in ((x, y, ww, 1), (x, y + hh - 1, ww, 1), (x, y, 1, hh), (x + ww - 1, y, 1, hh)):
                    g.rect(rx, ry, rw, rh, C_CYAN)
            else:
                im = self.glyph_image(self.tool) if not self.tool.startswith('@') else None
                if im and self.in_map(c, r):
                    g.img(im, x, y)
                for (rx, ry, rw, rh) in ((x, y, TILE, 1), (x, y + TILE - 1, TILE, 1), (x, y, 1, TILE), (x + TILE - 1, y, 1, TILE)):
                    g.rect(rx, ry, rw, rh, C_GOLD)
            if self.in_map(c, r):
                g.text('%d,%d' % (c, r), 4, VH - 8, C_DIM, 1)
        self.draw_ui()
        if self.modal:
            self.draw_modal()
        if self.edit:
            self.draw_text_box()

    def draw_ui(self):
        g = self.g
        VW, VH = g.VW, g.VH
        g.rect(0, 0, VW, self.TOP, '#0d0a1c')
        g.rect(0, self.TOP - 1, VW, 1, C_EDGE)
        mx, my = g.mx, g.my
        for (x, w, label, act) in self.top_layout():
            hot = my < self.TOP and x <= mx <= x + w
            g.rect(x, 2, w, 9, '#241f4a' if hot else '#15112b')
            g.text(label, x + 2, 4, C_GOLD if hot else C_TEXT, 1, shadow=False)
        g.rect(VW - 52, self.TOP, 52, VH - self.TOP, '#0d0a1c')
        g.rect(VW - 53, self.TOP, 1, VH - self.TOP, C_EDGE)
        for i, t in enumerate(PAL_SLOTS):
            x = VW - 50 + (i % 3) * 16
            y = 16 + (i // 3) * 16
            sel = t == self.tool or (t == '@RECT' and self.rect_mode)
            if sel:
                g.rect(x - 1, y - 1, 16, 16, C_GOLD)
            g.rect(x, y, 15, 15, '#15112b')
            if t.startswith('@'):
                g.text({'@HINT': 'T', '@ERASE': 'X', '@RECT': 'BOX'}[t], x + (4 if t != '@RECT' else 2), y + 5,
                       C_TEXT, 1, shadow=False)
            else:
                im = self.glyph_image(t)
                if im is not None:
                    if t == 'D':
                        g.img(im, x, y)
                    elif t in 'HI':
                        g.img(im, x + 2, y + 2)
                    elif t in 'oW':
                        g.img(im, x + 4, y + 4)
                    else:
                        g.img(im, x, y)
        lab = {'@HINT': 'SIGN TEXT', '@ERASE': 'ERASER', '@RECT': 'FILL BOX'}.get(self.tool, GLYPH_LABEL.get(self.tool, ''))
        g.text(lab, VW - 50, 164, C_TEXT, 1, shadow=False)
        g.text('BOX' if self.rect_mode else 'PAINT', VW - 50, 172, C_DIM, 1, shadow=False)
        g.rect(0, VH - self.BOT, VW - 52, self.BOT, '#0d0a1c')
        if self.msg[1] > 0:
            g.text(self.msg[0], 4, VH - 8, C_GOLD, 1, shadow=False)
        elif self.route:
            if self.route[0] == '...':
                g.text('CHECKING... %d' % self.route_prog, 4, VH - 8, C_CYAN, 1, shadow=False)
            else:
                g.text(self.route[0], VW // 2 - 50, VH - 8, C_CYAN if 'FOUND' in self.route[0] and 'NO' not in self.route[0] else C_RED, 1, shadow=False)
        g.text('%s  %dX%d' % (self.name, self.W, self.H) + ('*' if self.hash() != self.saved_hash else ''), VW - 54, VH - 8, C_DIM, 1, 'r', shadow=False)

    def draw_modal(self):
        g = self.g
        VW, VH = g.VW, g.VH
        w, h = 200, 140
        x, y = (VW - w) / 2.0, (VH - h) / 2.0
        g.panel(x, y, w, h)
        if self.modal == 'open':
            g.text('OPEN LEVEL', VW / 2.0, y + 6, C_GOLD, 2, 'c')
            if not self.files:
                g.text('NO LEVELS YET', VW / 2.0, y + 40, C_DIM, 1, 'c')
                g.text('SAVE ONE OR USE IMPORT', VW / 2.0, y + 50, C_FAINT, 1, 'c')
            off = max(0, self.mi - 8)
            for i, f in enumerate(self.files[off:off + 10]):
                sel = off + i == self.mi
                if sel:
                    g.text('>', x + 8, y + 24 + i * 10, C_GOLD)
                g.text(f[:-5], x + 18, y + 24 + i * 10, C_TEXT if sel else C_DIM)
            g.text('ENTER OPEN  C REMIX CAMPAIGN  DEL  ESC', VW / 2.0, y + h - 9, C_FAINT, 1, 'c')
            return
        g.text('LEVEL SETUP', VW / 2.0, y + 6, C_GOLD, 2, 'c')
        vals = [self.name, self.author, THEMES[self.theme]['name'], 'UPSIDE DOWN' if self.inv else 'NORMAL',
                'RING (WRAPS)' if self.ring else 'BOX (WALLS)', '%d SEC' % self.par, str(self.W), str(self.H),
                'PRESS ENTER', (self.music or {}).get('name', 'NONE') if self.music else 'NONE', '']
        for i, row in enumerate(self.PROP_ROWS):
            yy = y + 22 + i * 10
            sel = i == self.mi
            if sel:
                g.text('>', x + 6, yy, C_GOLD)
            g.text(row, x + 14, yy, C_TEXT if sel else C_DIM)
            g.text(vals[i], x + w - 8, yy, C_CYAN if sel else C_FAINT, 1, 'r')
        g.text('UP DOWN LEFT RIGHT  ENTER', VW / 2.0, y + h - 9, C_FAINT, 1, 'c')

    def draw_text_box(self):
        g = self.g
        VW, VH = g.VW, g.VH
        w, h = 220, 44
        x, y = (VW - w) / 2.0, VH / 2.0 - 22
        g.panel(x, y, w, h)
        g.text(self.edit['label'], x + 8, y + 6, C_GOLD)
        txt = self.edit['buf'] + ('_' if (g.t // 20) % 2 == 0 else ' ')
        g.text(txt, x + 8, y + 20, C_TEXT)
        g.text('ENTER OK  ESC CANCEL', x + w - 8, y + h - 9, C_FAINT, 1, 'r')


# ============================================================================
#  MUSIC MAKER
# ============================================================================
TTTM_HEAD = 'TTTM1'


def song_to_text(song):
    return TTTM_HEAD + '\n' + json.dumps(song, separators=(',', ':'))


def text_to_song(txt):
    txt = txt.lstrip('\ufeff')
    if not txt.startswith('TTTM'):
        raise ValueError('NOT A TTTM FILE')
    return clean_song(json.loads(txt.split('\n', 1)[1]))


CH_COL = {'lead': '#ff6ad5', 'arp': '#8ff7ff', 'bass': '#ffb04a', 'drum': '#7dffb0'}


class MusicMaker:
    GX, GY, CW, RH = 28, 50, 8, 6

    def __init__(self, game, song=None, path=None):
        self.g = game
        self.song = song or new_song()
        self.path = path
        self.pi = 0
        self.ch = 'lead'
        self.edit = None
        self.msg = ('', 0)
        self.modal = None
        self.mi = 0
        self.files = []
        self.drag = None
        self.playing = None          # ('pat'|'song', t0, total_steps) once audio is going
        self.pending = None
        self.render_n = 0
        self.saved = json.dumps(self.song, sort_keys=True)
        self.is_dirty = False

    # -- helpers ------------------------------------------------------------
    def say(self, s, n=150):
        self.msg = (s, n)

    @property
    def pat(self):
        return self.song['pats'][self.pi]

    def step_sec(self):
        return 60.0 / self.song['bpm'] / 4.0

    def hash(self):
        return json.dumps(self.song, sort_keys=True)

    def begin_text(self, label, initial, cb, maxlen=20):
        self.edit = dict(label=label, buf=initial, cb=cb, maxlen=maxlen)
        self.g.chars = []

    def upd_text(self):
        g, e = self.g, self.edit
        for ch in g.chars:
            if len(e['buf']) < e['maxlen']:
                e['buf'] += ch.upper()
        g.chars = []
        if 'backspace' in g.events:
            e['buf'] = e['buf'][:-1]
        if 'return' in g.events or 'kp_enter' in g.events:
            cb, buf = e['cb'], e['buf']
            self.edit = None
            cb(buf)
        elif 'escape' in g.events:
            self.edit = None

    # -- playback -------------------------------------------------------------
    def play(self, mode):
        self.stop()
        self.render_n += 1
        n = self.render_n
        song = json.loads(json.dumps(self.song))
        pi = self.pi
        self.say('RENDERING...', 400)

        def run():
            try:
                arr = render_song(song, pattern=pi) if mode == 'pat' else render_song(song)
                if n == self.render_n:
                    self.pending = (mode, arr, n)
            except Exception:
                self.say('RENDER FAILED')
        threading.Thread(target=run, daemon=True).start()

    def stop(self):
        self.render_n += 1
        self.pending = None
        self.playing = None
        self.g.audio.stop_music()
        self.g.audio.want = None

    def poll_play(self):
        if self.pending:
            mode, arr, n = self.pending
            self.pending = None
            self.g.audio.music_samples('mm%d' % n, arr)
            steps = self.song['steps'] * (2 if mode == 'pat' else len(self.song['order']))
            self.playing = (mode, time.perf_counter() + 0.15, steps, self.pi)
            self.say('PLAYING', 60)

    def playhead(self):
        if not self.playing:
            return None
        mode, t0, steps, pi = self.playing
        s = ((time.perf_counter() - t0) / self.step_sec())
        if s < 0:
            return None
        return s % steps

    # -- file ops ---------------------------------------------------------------
    def save(self):
        try:
            os.makedirs(MUSIC_DIR, exist_ok=True)
            p = self.path or os.path.join(MUSIC_DIR, safe_name(self.song['name']) + '.tttm')
            with open(p, 'w', encoding='utf-8') as f:
                f.write(song_to_text(self.song))
            self.path = p
            self.saved = self.hash()
            self.say('SAVED ' + os.path.basename(p).upper())
        except Exception:
            self.say('SAVE FAILED')

    def load(self, p):
        try:
            with open(p, 'r', encoding='utf-8') as f:
                self.song = text_to_song(f.read())
            self.path = p
            self.pi = 0
            self.saved = self.hash()
            self.stop()
            self.say('LOADED')
        except Exception:
            self.say('LOAD FAILED')

    def import_file(self):
        try:
            self.g.pick_file(('.tttm',), self._import_song, 'IMPORT SONG')
        except Exception:
            self.say('IMPORT FAILED')

    def set_theme(self):
        if self.hash() != self.saved or not self.path:
            self.save()
        if self.path:
            self.g.save['opts']['theme_song'] = os.path.basename(self.path)
            self.g.write_save()
            self.g.apply_theme_song()
            self.say('NOW THE GAME THEME!')

    # -- update -------------------------------------------------------------------

    def update(self):
        g = self.g
        self.poll_play()
        if self.msg[1] > 0:
            self.msg = (self.msg[0], self.msg[1] - 1)
        if self.edit:
            self.upd_text()
            g.mev = []
            return
        ev = g.events
        if self.modal == 'open':
            n = len(self.files)
            if 'escape' in ev:
                self.modal = None
            elif n:
                if 'up' in ev or 'w' in ev:
                    self.mi = (self.mi - 1) % n
                if 'down' in ev or 's' in ev:
                    self.mi = (self.mi + 1) % n
                if 'return' in ev:
                    self.load(os.path.join(MUSIC_DIR, self.files[self.mi]))
                    self.modal = None
                if 'delete' in ev:
                    try:
                        os.remove(os.path.join(MUSIC_DIR, self.files[self.mi]))
                        self.files = list_files(MUSIC_DIR, '.tttm')
                        self.mi = 0
                    except Exception:
                        pass
            g.mev = []
            return
        ctrl = bool(g.held & {'control_l', 'control_r'})
        if 'escape' in ev:
            self.leave()
            return
        if 'space' in ev:
            (self.stop() if self.playing or self.pending else self.play('pat'))
        elif 'return' in ev:
            self.play('song')
        elif ctrl and 's' in ev:
            self.save()
        elif 'bracketleft' in ev:
            self.pi = (self.pi - 1) % len(self.song['pats'])
        elif 'bracketright' in ev:
            self.pi = (self.pi + 1) % len(self.song['pats'])
        for k, name in (('1', 'lead'), ('2', 'arp'), ('3', 'bass'), ('4', 'drum')):
            if k in ev:
                self.ch = name
        for (kind, btn, x, y) in g.mev:
            if kind == 'down':
                self.click(btn, x, y)
            elif kind == 'up':
                self.drag = None
        g.mev = []
        if self.drag and 1 in g.mdown:
            st, row = self.cell(g.mx, g.my, clamp=True)
            n = self.drag
            n[2] = max(1, min(self.song['steps'] - n[0], st - n[0] + 1))
        elif self.drag:
            self.drag = None

    def leave(self):
        self.stop()
        if self.hash() != self.saved:
            self.save()
        self.g.leave_music()

    # -- layout ------------------------------------------------------------------------
    BTNS = [('NEW', 'new'), ('OPEN', 'open'), ('SAVE', 'save'), ('IMPORT', 'imp'), ('PLAY', 'play'),
            ('SONG', 'song'), ('STOP', 'stop'), ('RANDOM', 'rand'), ('THEME', 'theme'), ('EXIT', 'exit')]

    def btn_layout(self):
        x, out = 3, []
        for label, act in self.BTNS:
            w = len(label) * 4 + 4
            out.append((x, w, label, act))
            x += w + 2
        return out

    def settings(self):
        s = self.song
        ch = s['ch'][self.ch]
        return [('BPM', str(s['bpm']), 'bpm'), ('KEY', NOTE_NAMES[s['root'] % 12], 'root'),
                ('SCL', s['scale'].upper()[:5], 'scale'), ('STP', str(s['steps']), 'steps'),
                ('WAV', ch['wave'].upper(), 'wave'), ('VOL', str(ch['vol']), 'vol'),
                ('PW', '%d' % int(ch['duty'] * 100), 'duty')]

    def settings_layout(self):
        x, out = 3, []
        for label, val, key in self.settings():
            w = (len(label) + len(val) + 3) * 4 + 8
            out.append((x, 16, w, label, val, key))
            x += w + 2
        return out

    def cell(self, mx, my, clamp=False):
        st = int((mx - self.GX) // self.CW)
        row = int((my - self.GY) // self.RH)
        n = CH_ROWS[self.ch]
        if clamp:
            st = max(0, min(self.song['steps'] - 1, st))
            row = max(0, min(n - 1, row))
        return st, n - 1 - row if not clamp else n - 1 - row

    def click(self, btn, mx, my):
        g = self.g
        if my < 14:
            for (x, w, label, act) in self.btn_layout():
                if x <= mx <= x + w:
                    self.act(act)
                    return
            return
        if 15 <= my < 25:
            for (x, y, w, label, val, key) in self.settings_layout():
                if x <= mx <= x + w:
                    self.adjust(key, 1 if mx > x + w / 2 else -1)
                    return
            return
        if 25 <= my < 36:
            # channel tabs
            for i, name in enumerate(CH_NAMES):
                x = 3 + i * 44
                if x <= mx <= x + 42:
                    self.ch = name
            return
        if 36 <= my < 48:
            # pattern buttons
            n = len(self.song['pats'])
            for i in range(n):
                x = 3 + i * 14
                if x <= mx <= x + 12:
                    self.pi = i
                    return
            x = 3 + n * 14
            if n < 16 and x <= mx <= x + 12:
                self.song['pats'].append(dict(lead=[], arp=[], bass=[], drum=[]))
                self.pi = n
            elif n < 16 and x + 14 <= mx <= x + 26:
                self.song['pats'].append(json.loads(json.dumps(self.pat)))
                self.pi = n
            elif x + 28 <= mx <= x + 40:
                self.song['pats'][self.pi] = dict(lead=[], arp=[], bass=[], drum=[])
            return
        if my > g.VH - 22:
            # order row
            if mx < 40:
                self.song['order'].append(self.pi) if len(self.song['order']) < 64 else None
            elif mx < 80:
                if len(self.song['order']) > 1:
                    self.song['order'].pop()
            return
        # piano roll
        st, row = self.cell(mx, my)
        if not (0 <= st < self.song['steps'] and 0 <= row < CH_ROWS[self.ch]):
            return
        notes = self.pat[self.ch]
        hit = [n for n in notes if n[1] == row and n[0] <= st < n[0] + n[2]]
        if btn == 3 or hit:
            for n in hit:
                notes.remove(n)
            return
        if self.ch == 'drum':
            notes[:] = [n for n in notes if not (n[0] == st and n[1] == row)]
        note = [st, row, 1]
        notes.append(note)
        self.drag = note if self.ch != 'drum' else None
        self.preview_note(row)

    def preview_note(self, row):
        pass

    def adjust(self, key, d):
        s = self.song
        ch = s['ch'][self.ch]
        if key == 'bpm':
            s['bpm'] = max(50, min(220, s['bpm'] + 2 * d * (5 if self.g.held & {'shift_l', 'shift_r'} else 1)))
        elif key == 'root':
            s['root'] = max(24, min(48, s['root'] + d))
        elif key == 'scale':
            s['scale'] = SONG_SCALES[(SONG_SCALES.index(s['scale']) + d) % len(SONG_SCALES)]
        elif key == 'steps':
            s['steps'] = 16 if s['steps'] == 32 else 32
            for p in s['pats']:
                for c in CH_NAMES:
                    p[c] = [n for n in p[c] if n[0] < s['steps']]
                    for n in p[c]:
                        n[2] = min(n[2], s['steps'] - n[0])
        elif key == 'wave':
            ch['wave'] = WAVES[(WAVES.index(ch['wave']) + d) % len(WAVES)]
        elif key == 'vol':
            ch['vol'] = max(0, min(10, ch['vol'] + d))
        elif key == 'duty':
            ch['duty'] = max(0.125, min(0.5, ch['duty'] + 0.125 * d))

    def act(self, a):
        if a == 'new':
            self.stop()
            self.song = new_song()
            self.path = None
            self.pi = 0
            self.saved = self.hash()
        elif a == 'open':
            self.files = list_files(MUSIC_DIR, '.tttm')
            self.modal = 'open'
            self.mi = 0
        elif a == 'save':
            if self.song['name'] == 'MY SONG' and not self.path:
                self.begin_text('SONG NAME', self.song['name'],
                                lambda s: (self.song.__setitem__('name', s.strip() or 'MY SONG'), self.save()))
            else:
                self.save()
        elif a == 'imp':
            self.import_file()
        elif a == 'play':
            self.play('pat')
        elif a == 'song':
            self.play('song')
        elif a == 'stop':
            self.stop()
        elif a == 'rand':
            self.stop()
            moods = list(MOODS.keys())
            seed = random.randrange(1, 10 ** 6)
            self.song = generate_song(seed, random.choice(moods))
            self.pi = 0
            self.say('RANDOM SONG')
        elif a == 'theme':
            self.set_theme()
        elif a == 'exit':
            self.leave()

    # -- drawing --------------------------------------------------------------------------
    def draw(self):
        g = self.g
        VW, VH = g.VW, g.VH
        g.rect(0, 0, VW, VH, '#07060f')
        g.rect(0, 0, VW, 14, '#0d0a1c')
        mx, my = g.mx, g.my
        for (x, w, label, act) in self.btn_layout():
            hot = my < 14 and x <= mx <= x + w
            g.rect(x, 2, w, 9, '#241f4a' if hot else '#15112b')
            g.text(label, x + 2, 4, C_GOLD if hot else C_TEXT, 1, shadow=False)
        for (x, y, w, label, val, key) in self.settings_layout():
            g.rect(x, 16, w, 9, '#15112b')
            g.text('< %s %s >' % (label, val), x + 3, 18, C_TEXT, 1, shadow=False)
        for i, name in enumerate(CH_NAMES):
            x = 3 + i * 44
            sel = name == self.ch
            g.rect(x, 27, 42, 8, CH_COL[name] if sel else '#15112b')
            g.text(name.upper(), x + 21, 29, '#000000' if sel else CH_COL[name], 1, 'c', shadow=False)
        n = len(self.song['pats'])
        for i in range(n):
            x = 3 + i * 14
            sel = i == self.pi
            g.rect(x, 38, 12, 9, C_GOLD if sel else '#15112b')
            g.text(str(i + 1), x + 6, 40, '#000000' if sel else C_DIM, 1, 'c', shadow=False)
        x = 3 + n * 14
        if n < 16:
            g.rect(x, 38, 12, 9, '#1d3a2a')
            g.text('+', x + 6, 40, C_TEXT, 1, 'c', shadow=False)
            g.rect(x + 14, 38, 12, 9, '#1d2a3a')
            g.text('C', x + 20, 40, C_TEXT, 1, 'c', shadow=False)
        g.rect(x + 28, 38, 12, 9, '#3a1d2a')
        g.text('X', x + 34, 40, C_TEXT, 1, 'c', shadow=False)
        # roll
        steps = self.song['steps']
        rows = CH_ROWS[self.ch]
        col = CH_COL[self.ch]
        for r in range(rows):
            y = self.GY + (rows - 1 - r) * self.RH
            deg = r % 7
            shade = '#14102a' if deg in (0, 2, 4) else '#0f0c1e'
            if self.ch == 'drum':
                shade = '#14102a' if r % 2 == 0 else '#0f0c1e'
            g.rect(self.GX, y, steps * self.CW, self.RH, shade)
            if self.ch == 'drum':
                g.text(DRUM_NAMES[r], 2, y, C_DIM, 1, shadow=False)
            else:
                pitch = song_pitch(self.song, self.ch, r)
                g.text(NOTE_NAMES[pitch % 12] + str(pitch // 12 - 1), 2, y, col if deg == 0 else C_FAINT, 1, shadow=False)
        for s in range(steps + 1):
            g.rect(self.GX + s * self.CW, self.GY, 1, rows * self.RH, '#2a2450' if s % 4 == 0 else '#1a1634')
        for (st, row, ln) in self.pat[self.ch]:
            y = self.GY + (rows - 1 - row) * self.RH
            g.rect(self.GX + st * self.CW + 1, y + 1, ln * self.CW - 1, self.RH - 1, col)
        # ghost of other channels (dim)
        for other in CH_NAMES:
            if other == self.ch or other == 'drum' or self.ch == 'drum':
                continue
        ph = self.playhead()
        if ph is not None and self.playing and (self.playing[0] == 'song' or self.playing[3] == self.pi):
            pos = ph % steps if self.playing[0] == 'pat' else ph
            if self.playing[0] == 'song':
                bar = int(ph // steps)
                if self.song['order'][bar % len(self.song['order'])] != self.pi:
                    pos = None
                else:
                    pos = ph % steps
            if pos is not None:
                g.rect(self.GX + pos * self.CW, self.GY, 1, rows * self.RH, '#ffffff')
        # order row
        oy = VH - 20
        g.rect(0, oy, VW, 20, '#0d0a1c')
        g.rect(3, oy + 2, 36, 9, '#1d3a2a')
        g.text('+ORDER', 5, oy + 4, C_TEXT, 1, shadow=False)
        g.rect(41, oy + 2, 36, 9, '#3a1d2a')
        g.text('-ORDER', 43, oy + 4, C_TEXT, 1, shadow=False)
        g.text('ORDER ' + ' '.join(str(i + 1) for i in self.song['order'][:28]), 82, oy + 4, C_DIM, 1, shadow=False)
        info = self.msg[0] if self.msg[1] > 0 else 'SPACE PLAY  ENTER SONG  [ ] PATTERN  1-4 CHANNEL  RIGHT CLICK ERASE'
        g.text(info, 4, oy + 13, C_GOLD if self.msg[1] > 0 else C_FAINT, 1, shadow=False)
        g.text(self.song['name'] + ('*' if self.hash() != self.saved else ''), VW - 4, 28, C_DIM, 1, 'r', shadow=False)
        if self.modal == 'open':
            w, h = 180, 120
            x, y = (VW - w) / 2.0, (VH - h) / 2.0
            g.panel(x, y, w, h)
            g.text('OPEN SONG', VW / 2.0, y + 6, C_GOLD, 2, 'c')
            if not self.files:
                g.text('NO SONGS YET', VW / 2.0, y + 40, C_DIM, 1, 'c')
            off = max(0, self.mi - 8)
            for i, f in enumerate(self.files[off:off + 10]):
                sel = off + i == self.mi
                if sel:
                    g.text('>', x + 8, y + 24 + i * 9, C_GOLD)
                g.text(f[:-5], x + 18, y + 24 + i * 9, C_TEXT if sel else C_DIM)
        if self.edit:
            w, h = 220, 44
            x, y = (VW - w) / 2.0, VH / 2.0 - 22
            g.panel(x, y, w, h)
            g.text(self.edit['label'], x + 8, y + 6, C_GOLD)
            g.text(self.edit['buf'] + ('_' if (g.t // 20) % 2 == 0 else ' '), x + 8, y + 20, C_TEXT)


# ============================================================================
#  STORY MODE - art, characters, scripts, world data
# ============================================================================
PAGE_ROWS = ("..pppp..", ".pPPPPp.", "pPkkkkPp", "pPPPPPPp", "pPkkkkPp", "pPPPPPPp", ".pPPPPp.", "..pppp..")


def _disc(g, cx, cy, rx, ry, col):
    for y in range(len(g)):
        for x in range(len(g[0])):
            if ((x - cx) / float(rx)) ** 2 + ((y - cy) / float(ry)) ** 2 <= 1.0:
                g[y][x] = col


def _rect(g, x0, y0, x1, y1, col):
    for y in range(max(0, y0), min(len(g) - 1, y1) + 1):
        for x in range(max(0, x0), min(len(g[0]) - 1, x1) + 1):
            g[y][x] = col


def _outline(g, col):
    h, w = len(g), len(g[0])
    pts = []
    for y in range(h):
        for x in range(w):
            if g[y][x] is None:
                for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                    xx, yy = x + dx, y + dy
                    if 0 <= xx < w and 0 <= yy < h and g[yy][xx] is not None:
                        pts.append((x, y))
                        break
    for x, y in pts:
        g[y][x] = col


def g_boss(kind, th, f):
    T = THEMES[th]
    g = blank(40, 40)
    acc = T['accent']
    dark = T['mortar']
    body = T['stones'][1]
    hi = T['hi']
    lite = T['lip1']
    glow = blend(acc, '#ffffff', 0.5 if f else 0.15)
    if kind == 0:      # chandelier
        _rect(g, 19, 0, 20, 7, '#4a4380')
        for y in range(7, 30):
            hw = int(3 + (y - 7) * 0.8)
            _rect(g, 20 - hw, y, 19 + hw, y, body if (y // 3) % 2 else hi)
        _rect(g, 2, 14, 37, 16, lite)
        for cx in (3, 11, 19, 27, 35):
            _rect(g, cx, 10, cx + 2, 13, '#d8d4c4')
            _rect(g, cx, 7 - f, cx + 2, 9, '#ffe27a')
            g[6 - f][cx + 1] = '#ff8a2a'
        _rect(g, 14, 18, 17, 19, '#ffffff')
        _rect(g, 23, 18, 26, 19, '#ffffff')
        _disc(g, 20, 25, 4, 4, glow)
    elif kind == 1:    # bone choir
        _disc(g, 20, 16, 14, 12, '#d8d4c4')
        _rect(g, 12, 25, 28, 34, '#c4c0b0')
        for x in range(13, 28, 3):
            _rect(g, x, 27, x, 34, dark)
        _disc(g, 14, 15, 4, 4, dark)
        _disc(g, 26, 15, 4, 4, dark)
        _disc(g, 14, 15, 2, 2, glow)
        _disc(g, 26, 15, 2, 2, glow)
        _rect(g, 19, 20, 20, 22, dark)
        _disc(g, 20, 30, 3, 3, glow)
    elif kind == 2:    # smelter
        _rect(g, 14, 1 - 0, 21, 12, '#4a4380')
        _rect(g, 6, 12, 34, 38, body)
        _rect(g, 6, 12, 34, 14, hi)
        for (x, y) in ((8, 16), (32, 16), (8, 34), (32, 34)):
            _rect(g, x, y, x + 1, y + 1, lite)
        _rect(g, 12, 22, 28, 33, dark)
        _rect(g, 13, 24 - f, 27, 33, acc)
        _rect(g, 15, 27 - f, 25, 33, '#ffe27a')
        _rect(g, 11, 16, 16, 17, '#ffe27a')
        _rect(g, 24, 16, 29, 17, '#ffe27a')
    elif kind == 3:    # glacier eye
        for y in range(40):
            for x in range(40):
                if abs(x - 19.5) / 18.0 + abs(y - 19.5) / 20.0 <= 1.0:
                    g[y][x] = lite if (x + y) % 7 == 0 else body
        _disc(g, 20, 20, 10, 7, '#f0f8ff')
        _disc(g, 20, 20, 5, 5, acc)
        _disc(g, 20, 20, 2, 3, '#05040a')
        _rect(g, 19, 18, 20, 19, glow)
    elif kind == 4:    # hollow child
        _disc(g, 20, 13, 10, 10, '#2a1a40')
        _disc(g, 16, 14, 2, 2, '#ffffff')
        _disc(g, 24, 14, 2, 2, '#ffffff')
        _rect(g, 19, 19, 21, 21, '#05040a')
        for y in range(22, 39):
            hw = 4 + (y - 22) // 2
            _rect(g, 20 - hw, y, 19 + hw, y, '#3a2858' if y % 4 else '#2a1a40')
        _disc(g, 20, 30, 3 + f, 3 + f, glow)
        _disc(g, 6, 28, 3, 3, '#e8e0f0')
        _disc(g, 34, 28, 3, 3, '#e8e0f0')
    elif kind == 5:    # pendulum clock
        _rect(g, 19, 0, 20, 4, '#4a4380')
        _disc(g, 20, 21, 18, 18, '#a8873a')
        _disc(g, 20, 21, 15, 15, '#f0e8d0')
        for i in range(12):
            a = i * math.pi / 6
            g[int(21 - 13 * math.cos(a))][int(20 + 13 * math.sin(a))] = '#3a3020'
        a = f * 0.6
        for r in range(0, 11):
            g[int(21 - r * math.cos(a))][int(20 + r * math.sin(a))] = '#3a3020'
        for r in range(0, 8):
            g[int(21 - r * math.cos(a + 2.1))][int(20 + r * math.sin(a + 2.1))] = '#3a3020'
        _disc(g, 20, 21, 3, 3, glow)
    else:              # the turning
        _disc(g, 20, 20, 19, 19, '#1a1030')
        for i in range(16):
            a = i * math.pi / 8 + f * 0.1
            _rect(g, int(19 + 18 * math.cos(a)) - 1, int(19 + 18 * math.sin(a)) - 1,
                  int(19 + 18 * math.cos(a)) + 1, int(19 + 18 * math.sin(a)) + 1, '#a56bff')
        _disc(g, 20, 20, 13, 13, '#2d1850')
        _disc(g, 20, 20, 9, 9, acc)
        _disc(g, 20, 20, 7, 3, '#ffffff')
        _disc(g, 20, 20, 2, 3, '#05040a')
        for (x, y) in ((8, 8), (30, 11), (10, 30), (31, 29)):
            _rect(g, x, y, x + 1, y + 3, lite)
    _outline(g, '#0a0814')
    return g


NPC_STYLES = {
    'mira': dict(pal=dict(c='#c2602a', d='#7a3418', h='#ff9a4a', b='#8ff7ff', e='#ffffff'),
                 extra=[(6, 5, '#ffe27a'), (9, 5, '#ffe27a'), (5, 5, '#8a5a20'), (10, 5, '#8a5a20')]),
    'tock': dict(pal=dict(c='#6a6a80', d='#3a3a4a', h='#9a9ab8', b='#d8d4c4', e='#8ff7ff'),
                 extra=[(6, 7, '#e8e8f0'), (7, 7, '#e8e8f0'), (8, 7, '#e8e8f0'), (9, 7, '#e8e8f0'),
                        (7, 8, '#e8e8f0'), (8, 8, '#e8e8f0')]),
    'brin': dict(pal=dict(c='#3a8a5a', d='#1f4a30', h='#6acf8a', b='#ffd75a', e='#ffffff'), extra=[]),
    'cog': dict(pal=dict(c='#8a9aa8', d='#4a5a68', h='#c8d8e8', b='#ff6a6a', e='#ff3b3b'),
                extra=[(7, 1, '#ff6a6a'), (8, 1, '#ff6a6a'), (7, 0, '#c8d8e8')]),
    'bellows': dict(pal=dict(c='#7a5a3a', d='#4a3420', h='#a8825a', b='#ff9a4a', e='#ffe27a'),
                    extra=[(5, 3, '#4a3420'), (10, 3, '#4a3420')]),
    'ghost': dict(pal=dict(c='#6a88b8', d='#3a5078', h='#a8c8f0', b='#ffffff', e='#ffffff'), extra=[]),
}


def g_npc(kind, face):
    st = NPC_STYLES[kind]
    rows = list(PL_HEAD)
    eyes = 'efefff' if face < 0 else 'fffefe'
    rows[5] = '....k' + eyes + 'k....'
    rows = rows + PL_LEGS['stand']
    pal = dict(PL_BASE_PAL)
    pal.update(st['pal'])
    g = from_ascii(rows, pal)
    for (x, y, c) in st['extra']:
        g[y][x] = c
    return g


def g_wisp_pal(f):
    return from_ascii(ORB_ROWS, ORB_PAL if f == 0 else {'t': '#1a8f9b', 'T': '#5ff0fb', 'W': '#ffffff', 'd': '#127585'})


class AssetsX(Assets):
    def door_icon(self, th):
        return self.get(('dooric', th), lambda: g_door(THEMES[th], 0)[:16])

    def page(self):
        return self.get('page', lambda: from_ascii(PAGE_ROWS, {'p': '#a8873a', 'P': '#f0e0a8', 'k': '#6a5a30'}))

    def boss(self, kind, th, f):
        return self.get(('boss', kind, th, f), lambda: g_boss(kind, th, f))

    def npc(self, kind, face):
        return self.get(('npc', kind, face), lambda: g_npc(kind, face))

    def portrait(self, who, th=0):
        """returns (image, w, h) in logical px or None"""
        if who in NPC_STYLES:
            def mk():
                g = g_npc(who, 1)
                return [row[2:14] for row in g[1:11]]
            return self.get(('port', who), lambda: mk()) if False else (self._port(who), 36, 30)
        return None

    def _port(self, who):
        key = ('port3', who)
        if key not in self.cache:
            g = g_npc(who, 1)
            self.cache[key] = self.build([row[2:14] for row in g[1:11]], self.S * 3)
        return self.cache[key]

    def port_player(self, skin):
        key = ('portp', skin)
        if key not in self.cache:
            g = g_player('stand', 1, DOWN, skin)
            self.cache[key] = self.build([row[2:14] for row in g[1:11]], self.S * 3)
        return self.cache[key]

    def port_orb(self):
        key = 'porto'
        if key not in self.cache:
            self.cache[key] = self.build(g_wisp_pal(1), self.S * 4)
        return self.cache[key]


# ---------------------------------------------------------------------------
#  Characters, bosses, shop, quests, pages
# ---------------------------------------------------------------------------
SPEAKER_COL = {'WANDERER': '#a56bff', 'MIRA': '#ff9a4a', 'TOCK': '#9a9ab8', 'WISP': '#8ff7ff', 'BRIN': '#6acf8a',
               'COG': '#ff6a6a', 'BELLOWS': '#a8825a', 'GHOST': '#a8c8f0', 'TOWER': '#f0c75e', '': '#f0c75e'}

REGIONS = [
    dict(id='r1', name='THE FOYER WING', theme=0, boss='b1', inv=False, seed=701,
         rooms=['HALL', 'DOORS', 'CAROUSEL', 'SPRINGS', 'CEILINGS', 'HALL', 'DOORS', 'PILLAR'],
         wisps=0, saws=0, hints=True, need=0, sub='WHERE THE LIGHTS STILL BURN'),
    dict(id='r2', name='THE CATACOMBS', theme=1, boss='b2', inv=False, seed=702,
         rooms=['CEILINGS', 'PILLAR', 'DOORS', 'SPRINGS', 'CRUMBLE', 'PILLAR', 'CEILINGS', 'SPIRAL', 'DOORS'],
         wisps=0, saws=0, hints=False, need=1, sub='THE DEAD KEEP THE TIME'),
    dict(id='r3', name='THE FURNACE', theme=2, boss='b3', inv=False, seed=703,
         rooms=['WINDRUN', 'CRUMBLE', 'DOORS', 'SPRINGS', 'CEILINGS', 'WINDRUN', 'SPIRAL', 'CRUMBLE', 'PILLAR'],
         wisps=0, saws=1, hints=False, need=1, sub='WHERE THE GEARS ARE FORGED'),
    dict(id='r4', name='THE FROST', theme=3, boss='b4', inv=True, seed=704,
         rooms=['SPRINGS', 'PILLAR', 'WINDRUN', 'DOORS', 'SPIRAL', 'CRUMBLE', 'FLIPFLOP', 'PILLAR', 'CEILINGS'],
         wisps=0, saws=1, hints=False, need=1, sub='EVERYTHING HERE HANGS UPSIDE DOWN'),
    dict(id='r5', name='THE VOID', theme=4, boss='b5', inv=False, seed=705,
         rooms=['FLIPFLOP', 'SPIRAL', 'GUARDS', 'PILLAR', 'CRUMBLE', 'WINDRUN', 'FLIPFLOP', 'DOORS', 'SPIRAL'],
         wisps=1, saws=1, hints=False, need=1, sub='WHERE UP FORGOT ITS NAME'),
    dict(id='r6', name='THE CLOCKWORK', theme=5, boss='b6', inv=True, seed=706,
         rooms=['DOORS', 'WINDRUN', 'FLIPFLOP', 'SPIRAL', 'PILLAR', 'GUARDS', 'CRUMBLE', 'FLIPFLOP', 'SPIRAL'],
         wisps=1, saws=1, hints=False, need=4, sub='THE HEART OF THE MACHINE'),
    dict(id='r7', name='THE SUMMIT', theme=4, boss='b7', inv=False, seed=707,
         rooms=['FLIPFLOP', 'SPIRAL', 'GUARDS', 'PILLAR', 'CRUMBLE', 'WINDRUN', 'FLIPFLOP', 'SPIRAL', 'GUARDS',
                'PILLAR', 'CRUMBLE', 'FLIPFLOP'],
         wisps=2, saws=1, hints=False, need=6, sub='THE LAST TURN'),
]
REGION = {r['id']: r for r in REGIONS}

BOSSES = {
    'b1': dict(name='THE CHANDELIER', kind=0, hp=18, size=(30, 26), theme=0, move='hover', patterns=[['rain'], ['rain', 'aim'], ['rain', 'aim', 'ring']], gear='SUN GEAR', reward=60),
    'b2': dict(name='THE BONE CHOIR', kind=1, hp=22, size=(28, 24), theme=1, move='orbit', patterns=[['aim'], ['aim', 'ring'], ['spiral', 'aim']], gear='BONE GEAR', reward=70),
    'b3': dict(name='THE SMELTER', kind=2, hp=26, size=(30, 30), theme=2, move='charge', patterns=[['trail'], ['trail', 'rain'], ['trail', 'rain', 'aim']], gear='EMBER GEAR', reward=80),
    'b4': dict(name='THE GLACIER EYE', kind=3, hp=28, size=(28, 28), theme=3, move='hover', patterns=[['spiral'], ['spiral', 'aim'], ['ring', 'spiral']], shift=['right', 'left'], gear='FROST GEAR', reward=90),
    'b5': dict(name='THE HOLLOW CHILD', kind=4, hp=30, size=(24, 28), theme=4, move='teleport', patterns=[['ring'], ['ring', 'aim'], ['spiral', 'ring', 'aim']], shift=['up', 'down'], gear='VOID GEAR', reward=100),
    'b6': dict(name='THE PENDULUM', kind=5, hp=34, size=(30, 30), theme=5, move='pendulum', patterns=[['saw'], ['saw', 'aim'], ['saw', 'ring', 'aim']], shift=['cw'], gear='TIME GEAR', reward=120),
    'b7': dict(name='THE TURNING', kind=6, hp=44, size=(32, 32), theme=4, move='mix', patterns=[['ring', 'aim'], ['spiral', 'rain', 'saw'], ['ring', 'spiral', 'aim', 'trail']], shift=['cw'], gear='THE HEART', reward=300),
}

SHOP = [
    ('heart', 'HEART CONTAINER', 'MAX HEARTS +1', [40, 60, 80, 110, 150]),
    ('double', 'AIR STEP BOOTS', 'JUMP AGAIN IN MIDAIR', [120]),
    ('dash', 'SPARK CLASP', 'DASH WITH SHIFT', [160]),
    ('lantern2', 'BRIGHT WICK', 'LANTERN DAMAGE +1', [150]),
    ('magnet', 'SOUL MAGNET', 'SOULS DRIFT TO YOU', [70]),
    ('cloak1', 'EMBER CLOAK', 'COSMETIC', [60]),
    ('cloak2', 'MOSS CLOAK', 'COSMETIC', [60]),
    ('cloak3', 'FROST CLOAK', 'COSMETIC', [60]),
    ('cloak4', 'GOLDEN CLOAK', 'COSMETIC', [80]),
    ('cloak5', 'VOID CLOAK', 'COSMETIC', [100]),
]

QUESTS = [
    dict(id='q_souls1', who='BRIN', title='SHINY THINGS I', desc='COLLECT 50 SOULS IN TOTAL', stat='souls_total', goal=50, reward=('souls', 30)),
    dict(id='q_souls2', who='BRIN', title='SHINY THINGS II', desc='COLLECT 150 SOULS IN TOTAL', stat='souls_total', goal=150, reward=('souls', 70)),
    dict(id='q_souls3', who='BRIN', title='SHINY THINGS III', desc='COLLECT 300 SOULS IN TOTAL', stat='souls_total', goal=300, reward=('heart', 1)),
    dict(id='q_pages1', who='TOCK', title='LOST PAGES I', desc='FIND 4 JOURNAL PAGES', stat='pages', goal=4, reward=('souls', 50)),
    dict(id='q_pages2', who='TOCK', title='LOST PAGES II', desc='FIND 8 JOURNAL PAGES', stat='pages', goal=8, reward=('souls', 100)),
    dict(id='q_pages3', who='TOCK', title='LOST PAGES III', desc='FIND ALL 12 PAGES', stat='pages', goal=12, reward=('heart', 1)),
    dict(id='q_gears', who='MIRA', title='THE SIX GEARS', desc='RECOVER ALL SIX GEARS', stat='gears', goal=6, reward=('souls', 150)),
]

PAGES = [
    ('THE FIRST TURN', 'THE TOWER WAS BUILT TO TURN. NOT TO STAND. A THING THAT DOES NOT MOVE IS ONLY A WALL.'),
    ('KEEPER LOG 1', 'SIX WARDENS WERE CHOSEN, ONE FOR EACH WING. EACH WAS GIVEN A GEAR AND A PROMISE.'),
    ('KEEPER LOG 2', 'THE PROMISE WAS SIMPLE: KEEP IT TURNING, NO MATTER HOW TIRED YOU GET.'),
    ('THE CHANDELIER', 'THE FOYER WARDEN LIT A THOUSAND CANDLES. SHE WAS AFRAID OF THE DARK. WHO ISN\'T?'),
    ('THE CHOIR', 'THE DEAD SING TO KEEP TIME. WHEN THE TOWER STOPPED, THEY KEPT SINGING. THEY DID NOT KNOW HOW TO STOP.'),
    ('THE SMELTER', 'EVERY GEAR IN THE TOWER WAS FORGED HERE. THE FIRE NEVER WENT OUT. IT ONLY GOT LONELY.'),
    ('THE GLACIER', 'IN THE FROST WING, TIME IS SLOW AND THE VIEW IS GOOD. IT IS EASY TO FORGET TO LEAVE.'),
    ('THE VOID', 'THE VOID IS WHERE GRAVITY GOES WHEN NOBODY LOOKS. THE CHILD THERE HAS NEVER STOPPED FALLING.'),
    ('THE PENDULUM', 'TICK. TOCK. THE CLOCKWORK WARDEN COUNTED EVERY SECOND OF EVERY DAY. SHE IS VERY TIRED OF NUMBERS.'),
    ('THE KEY', 'THE WINDING KEY WAS NEVER LOST. IT WAS WORN. THE KEEPER KEPT IT CLOSE, AND THEN WALKED AWAY.'),
    ('THE HEART', 'THE HEART OF THE TOWER IS NOT A MACHINE. IT HAS BEEN LISTENING THE WHOLE TIME.'),
    ('ROUND AND ROUND', 'UP AND DOWN, ROUND AND ROUND. NOTHING ENDS. IT ONLY TURNS. THAT IS NOT A CURSE. THAT IS A GIFT.'),
]


def sc(who, text):
    return ('say', who, text)


def script_prologue():
    return [('bg', 'tower'), ('fade_in', 40),
            sc('', 'THE TURNING TOWER STOOD AT THE CENTRE OF THE WORLD.'),
            sc('', 'IT TURNED. UP AND DOWN. ROUND AND ROUND. AND THE WORLD TURNED WITH IT.'),
            sc('', 'THEN, ONE NIGHT, IT STOPPED.'),
            ('shake', 24), ('sfx', 'death'),
            sc('', 'GRAVITY FORGOT WHICH WAY WAS DOWN. FLOORS BECAME WALLS. WALLS BECAME SKY.'),
            sc('', 'AND SOMEONE WOKE UP IN THE CONCOURSE, THE LAST QUIET RING OF THE TOWER.'),
            ('bg', 'world'),
            sc('WISP', 'HEY. HEY! YOU\'RE AWAKE!'),
            sc('WANDERER', '...'),
            sc('WISP', 'I\'M WISP. I FOUND YOU FACE DOWN. OR UP. HONESTLY NOBODY KNOWS ANY MORE.'),
            sc('WISP', 'THIS IS THE CONCOURSE. IT STILL TURNS, A LITTLE. THE REST OF THE TOWER... DOESN\'T.'),
            sc('WISP', 'GO TALK TO MIRA. SHE\'S THE ONE WITH THE GOGGLES. SHE FIXES THINGS.'),
            sc('WISP', 'A D TO MOVE. SPACE TO JUMP. E TO TALK. TOUCH CRYSTALS TO TURN GRAVITY. YOU\'LL SEE.'),
            ('flag', 'prologue')]


def script_mira_intro():
    return [sc('MIRA', 'WELL, LOOK AT THAT. A WALKING CLOAK. DO YOU COME WITH A PERSON INSIDE?'),
            sc('WANDERER', '...'),
            sc('MIRA', 'STRONG, SILENT TYPE. FINE. I\'M MIRA. I MAKE THINGS, FIX THINGS, AND SELL THINGS TO PEOPLE WHO BREAK THINGS.'),
            sc('WISP', 'SHE\'S NICE. MOSTLY.'),
            sc('MIRA', 'THE TOWER STOPPED TURNING SIX NIGHTS AGO. THE SIX WARDENS WHO KEPT ITS GEARS ROLLING WENT QUIET. THEN THEY WENT STRANGE.'),
            sc('MIRA', 'EACH ONE STILL HOLDS A GEAR. BRING ME ALL SIX, WIND THE HEART AT THE SUMMIT, AND THE TOWER TURNS AGAIN.'),
            sc('MIRA', 'YOU\'LL NEED THIS. A SOUL LANTERN. PRESS X TO THROW LIGHT. WARDENS HATE IT.'),
            ('give', 'lantern'), ('sfx', 'clear'),
            sc('MIRA', 'SOULS YOU FIND OUT THERE ARE MONEY AROUND HERE. SPEND THEM AT MY SHOP. TALK TO ME ANY TIME.'),
            sc('WISP', 'THE GATES ARE ON THE LOWER RING. START WITH THE FOYER WING. IT\'S THE POLITE ONE.'),
            ('flag', 'met_mira')]


def script_brin(story):
    n = story['souls_total']
    if 'met_brin' not in story['flags']:
        return [sc('BRIN', 'HI! HI HI HI! ARE YOU THE NEW HERO? YOU LOOK LIKE A HERO. A SHORT ONE.'),
                sc('BRIN', 'I COLLECT SOULS. THE LITTLE GLOWY ONES. THEY\'RE SO PRETTY.'),
                sc('BRIN', 'IF YOU FIND LOTS, TELL ME! I\'LL GIVE YOU STUFF!'),
                ('flag', 'met_brin')]
    return [sc('BRIN', 'YOU\'VE COLLECTED %d SOULS SO FAR! KEEP GOING, KEEP GOING!' % n), ('quests',)]


def script_tock(story):
    g = len(story['gears'])
    if 'met_tock' not in story['flags']:
        return [sc('TOCK', 'AH. A KEEPER\'S CLOAK. HOW CURIOUS. I HAVEN\'T SEEN ONE IN... A LONG TURN.'),
                sc('TOCK', 'I\'M TOCK. I WRITE DOWN WHAT THE TOWER DOES. LATELY IT DOES NOTHING. BORING WORK.'),
                sc('TOCK', 'PAGES OF MY JOURNAL BLEW AWAY WHEN IT STOPPED. IF YOU FIND ANY, BRING THEM TO ME AND I\'LL PAY.'),
                ('flag', 'met_tock')]
    if g >= 6:
        return [sc('TOCK', 'YOU HAVE ALL SIX. THEN GO UP, KEEPER. BUT REMEMBER: THE HEART IS NOT YOUR ENEMY.'),
                sc('TOCK', 'IT IS TIRED. LIKE THE REST OF US.'), ('quests',)]
    if g >= 3:
        return [sc('TOCK', 'THE WARDENS ARE NOT VILLAINS. THEY WERE ASKED TO HOLD A TURN THAT NEVER ENDED.'),
                sc('TOCK', 'THE CLOAK YOU WEAR... DOES IT HAVE A KEY SEWN IN? NEVER MIND. I\'M OLD.'), ('quests',)]
    return [sc('TOCK', 'THE TOWER IS A RING. THAT\'S WHY YOU CAN WALK ROUND AND ROUND. LEAVE A FLOOR, FIND ANOTHER.'),
            sc('TOCK', 'AND THE CRYSTALS... THOSE ARE JUST THE TOWER CHANGING ITS MIND ABOUT DOWN.'), ('quests',)]


def script_wisp(story):
    g = len(story['gears'])
    if 'got_lantern' not in story['flags']:
        return [sc('WISP', 'MIRA\'S ON THE MIDDLE RING. USE THE UPDRAFT, THE GLOWING COLUMN, TO RISE.')]
    if g == 0:
        return [sc('WISP', 'THE FOYER WING IS THE GATE ON THE LEFT. YOU CAN DO THIS. PROBABLY.')]
    if g < 6:
        return [sc('WISP', '%d GEARS DOWN. THE GATES TO THE OTHER WINGS ARE OPEN NOW. PICK ANY.' % g),
                sc('WISP', 'THE CLOCKWORK WING NEEDS FOUR GEARS. THE SUMMIT NEEDS ALL SIX.')]
    return [sc('WISP', 'THE SUMMIT GATE IS OPEN. I\'M SCARED. I\'M COMING WITH YOU ANYWAY.')]


def script_cog(story):
    return [sc('COG', 'BEEP. I AM CHECKING THE FLOOR. THE FLOOR IS... SIDEWAYS TODAY.'),
            sc('COG', 'BEEP. TIP: IF YOU FALL LEFT FOREVER, YOU ARE ON A RING. THE RING IS FOREVER.')]


def script_bellows(story):
    return [sc('BELLOWS', 'THE FIRE\'S NOT GONE OUT, YOU KNOW. IT\'S WAITING. LIKE WE ALL ARE.'),
            sc('BELLOWS', 'IF YOU SEE THE SMELTER, TELL HIM WE MISS HIM.')]


def script_ghost(story):
    n = len(story['gears'])
    return [sc('GHOST', 'I USED TO BE THE CLOCKMAKER. NOW I JUST STAND HERE. IT\'S A FINE JOB.'),
            sc('GHOST', 'THE TOWER REMEMBERS EVERYONE WHO TURNED IT. %d GEARS. THE REST IS UP TO YOU.' % n)]


BOSS_INTRO = {
    'b1': [sc('???', 'WHO DISTURBS THE LIGHT?'), sc('THE CHANDELIER', 'I HAVE BURNED SINCE THE FIRST TURN. I DO NOT KNOW HOW TO GO OUT.'),
           sc('WISP', 'SHE\'S... VERY SPARKLY. AND VERY ANGRY.')],
    'b2': [sc('THE BONE CHOIR', 'WE SING FOR THE STOPPED. WE SING FOR THE STILL.'), sc('THE BONE CHOIR', 'JOIN US. THE SONG HAS NO LAST NOTE.')],
    'b3': [sc('THE SMELTER', 'FIRE DOES NOT TURN. FIRE JUST WAITS. AND I HAVE WAITED SO LONG.'), sc('WISP', 'IT\'S HOT IN HERE. I\'M A GHOST AND I\'M SWEATING.')],
    'b4': [sc('THE GLACIER EYE', 'EVERYTHING IS BEAUTIFUL WHEN IT STOPS. WHY WOULD YOU WIND IT?'), sc('THE GLACIER EYE', 'LOOK AT THE SNOW. IT HAS BEEN FALLING FOR A THOUSAND TURNS.')],
    'b5': [sc('THE HOLLOW CHILD', 'IF DOWN IS UP AND UP IS DOWN, WHICH WAY ARE YOU FALLING?'), sc('THE HOLLOW CHILD', 'COME PLAY. THE FLOOR IS LAVA. THE CEILING IS LAVA. EVERYTHING IS LAVA.')],
    'b6': [sc('THE PENDULUM', 'TICK. TOCK. YOU ARE LATE. YOU WERE ALWAYS LATE, KEEPER.'), sc('WISP', 'KEEPER?'), sc('THE PENDULUM', 'THE KEY IS SEWN IN YOUR CLOAK. I CAN HEAR IT TICKING.')],
    'b7': [sc('THE TURNING', 'I AM THE LAST TURN. I AM THE FIRST. I AM SO VERY TIRED, KEEPER.'), sc('THE TURNING', 'YOU LEFT ME HERE TO TURN ALONE. I FORGIVE YOU. BUT I CANNOT LET YOU WIND ME AGAIN.'),
           sc('WISP', 'IT\'S NOT ANGRY. IT\'S... CRYING?'), sc('THE TURNING', 'THEN SHOW ME WHY IT SHOULD TURN.')],
}
BOSS_OUTRO = {
    'b1': [sc('THE CHANDELIER', 'THANK YOU... TAKE MY GEAR. IT WAS HEAVY.'), ('gear', 'b1')],
    'b2': [sc('THE BONE CHOIR', 'THE SONG... ENDS? GOOD. IT WAS A VERY LONG VERSE.'), ('gear', 'b2')],
    'b3': [sc('THE SMELTER', 'I WAS ONLY KEEPING THE WORLD WARM. WAS THAT WRONG?'), sc('WANDERER', '...'), sc('THE SMELTER', 'NO. YOU UNDERSTAND. TAKE IT.'), ('gear', 'b3')],
    'b4': [sc('THE GLACIER EYE', '...THE SNOW IS MOVING AGAIN. HUH. I FORGOT IT COULD.'), ('gear', 'b4')],
    'b5': [sc('THE HOLLOW CHILD', 'I WAS ALWAYS FALLING. IT\'S NICE TO LAND.'), ('gear', 'b5')],
    'b6': [sc('THE PENDULUM', 'YOU WERE THE KEEPER. YOU LEFT. THE TOWER STOPPED.'), sc('WANDERER', '...'),
           sc('THE PENDULUM', 'GO UP. THE HEART WILL TELL YOU THE REST.'), ('gear', 'b6')],
    'b7': [sc('THE TURNING', '...THANK YOU. I REMEMBER NOW. I ASKED YOU TO LEAVE.'), sc('THE TURNING', 'I WANTED TO REST. BUT RESTING IS ALSO A KIND OF TURN.'),
           sc('WISP', 'SO... WE WIND IT, BUT GENTLY?'), sc('THE TURNING', 'WIND ME, KEEPER. NOT TO WORK. JUST TO BEAT.'), ('ending',)],
}
ENDING = [('fade_out', 40), ('bg', 'tower'), ('fade_in', 60), ('sfx', 'clear'),
          sc('', 'THE WANDERER PLACED THE KEY, AND TURNED IT.'), ('shake', 20),
          sc('', 'SOMEWHERE ABOVE, A GREAT ROUND SOUND BEGAN, LIKE A SLEEPER BREATHING.'),
          sc('', 'FLOORS FOUND THEIR FLOORS. WALLS REMEMBERED BEING WALLS.'),
          sc('', 'AND THE TOWER TURNED. UP AND DOWN. ROUND AND ROUND.'),
          sc('WISP', 'IT\'S TURNING. IT\'S TURNING! DID YOU SEE?'),
          sc('WISP', 'THE CONCOURSE IS GOING TO BE SO LOUD TOMORROW.'),
          sc('', 'NOTHING ENDS. IT ONLY TURNS.'),
          ('credits',)]
CREDITS = ['THE TURNING TOWER', '', 'A GMI GAME JAM 2026 ENTRY', 'SECRET THEME:', 'UP AND DOWN ROUND AND ROUND', '',
           'THANK YOU FOR PLAYING', '', 'THE CONCOURSE IS OPEN.', 'GO BACK. FIND EVERY PAGE.', 'SPEND YOUR SOULS.', 'KEEP IT TURNING.']
FINAL_PRE = [sc('WISP', 'THIS IS IT. THE SUMMIT.'), sc('WISP', 'WHATEVER HAPPENS... YOU WERE ALWAYS THE ONE WHO KEPT THINGS MOVING.')]


# ---------------------------------------------------------------------------
#  Hub rooms (towns) and boss arenas
# ---------------------------------------------------------------------------
def r_town1(rnd, spec):
    R = Room('TOWN1', 9, 22)
    R.diff = 0
    R.start = 14
    R.cp = None
    R.hint = None
    R.ents = [dict(t='npc', id='brin', c=19, r=8), dict(t='warp', to='r1', c=7, r=8),
              dict(t='warp', to='r2', c=10, r=8), dict(t='warp', to='r3', c=13, r=8),
              dict(t='npc', id='bellows', c=3, r=8), dict(t='lift', c=1, r=8)]
    R.put(24, 6, 'o')
    return R


def r_town2(rnd, spec):
    R = Room('TOWN2', 9, 22)
    R.diff = 0
    R.cp = None
    R.ents = [dict(t='npc', id='mira', c=11, r=8), dict(t='warp', to='r4', c=15, r=8),
              dict(t='warp', to='r5', c=18, r=8), dict(t='npc', id='cog', c=20, r=8),
              dict(t='lift', c=27, r=8)]
    return R


def r_town3(rnd, spec):
    R = Room('TOWN3', 9, 22)
    R.diff = 0
    R.cp = None
    R.door = 26
    R.ents = [dict(t='npc', id='tock', c=11, r=8), dict(t='warp', to='r6', c=15, r=8),
              dict(t='warp', to='r7', c=19, r=8), dict(t='npc', id='ghost', c=24, r=8),
              dict(t='lift', c=27, r=8)]
    return R


ROOMS['TOWN1'], ROOMS['TOWN2'], ROOMS['TOWN3'] = r_town1, r_town2, r_town3
HUB_SPEC = dict(name='THE CONCOURSE', sub='THE LAST QUIET RING', theme=0, rooms=['TOWN1', 'TOWN2', 'TOWN3'],
                seed=999, par=0, inv=False, hints=False, fixed=True)


def arena_data(bid):
    """22x12 boxed boss arena (fits on one screen)"""
    b = BOSSES[bid]
    W, H = 22, 12
    rows = [['.'] * W for _ in range(H)]

    def box(c0, r0, c1, r1, ch):
        for r in range(r0, r1 + 1):
            for c in range(c0, c1 + 1):
                rows[r][c] = ch
    box(0, 0, W - 1, 1, '#')
    box(0, 10, W - 1, 11, '#')
    box(0, 2, 1, 9, '#')
    box(20, 2, 21, 9, '#')
    if bid == 'b1':
        box(4, 6, 6, 6, '#'); box(15, 6, 17, 6, '#'); box(9, 4, 12, 4, '#')
    elif bid == 'b2':
        box(6, 7, 6, 9, '#'); box(10, 6, 11, 9, '#'); box(16, 7, 16, 9, '#')
    elif bid == 'b3':
        box(4, 6, 7, 6, '#'); box(14, 6, 17, 6, '#')
        for c in (10, 11):
            rows[9][c] = 'u'
    elif bid == 'b4':
        box(3, 5, 5, 5, '#'); box(16, 5, 18, 5, '#'); box(9, 7, 12, 7, '#')
    elif bid == 'b5':
        box(4, 6, 5, 6, '#'); box(16, 6, 17, 6, '#'); box(9, 3, 12, 3, '#'); box(9, 8, 12, 8, '#')
    elif bid == 'b6':
        box(4, 6, 6, 6, '#'); box(15, 6, 17, 6, '#'); box(9, 4, 12, 4, '#')
        rows[9][8] = 'S'; rows[9][13] = 'S'
    else:
        box(3, 6, 5, 6, '#'); box(16, 6, 18, 6, '#'); box(9, 4, 12, 4, '#'); box(9, 8, 12, 8, '#')
    rows[9][3] = 'P'
    return dict(fmt='TTTL', ver=1, name=b['name'], author='THE TOWER', theme=b['theme'], inv=False, ring=False,
                par=0, rows=[''.join(r) for r in rows], hints=[], music=None)


# ============================================================================
#  AUDIO additions (custom songs) + STORY RUNTIME
# ============================================================================
MOODS['hub'] = dict(bpm=(78, 88), scales=['dorian', 'minor'], duty=0.25, drums=0.5, arp=1.0)
MOODS['boss'] = dict(bpm=(124, 134), scales=['phrygian', 'harmonic'], duty=0.5, drums=1.35, arp=1.1)
MOODS['finale'] = dict(bpm=(134, 144), scales=['harmonic'], duty=0.25, drums=1.4, arp=1.2)


class AudioX(Audio):
    def music_samples(self, key, arr):
        try:
            path = os.path.join(self.dir, 'prev_%s.wav' % key)
            write_wav(path, arr)
            self.stop_music()
            self.music_ready[key] = path
            self.want = key
        except Exception:
            pass

    def music_song(self, key, song):
        if not self.ok or key == self.want:
            return
        self.want = key
        self.stop_music()
        h = hashlib.md5(json.dumps(song, sort_keys=True).encode()).hexdigest()[:12]
        path = os.path.join(self.dir, 'song_%s.wav' % h)
        if os.path.exists(path):
            self.music_ready[key] = path
            return

        def run():
            try:
                with self.gen_lock:
                    write_wav(path, render_song(song))
                self.music_ready[key] = path
            except Exception:
                pass
        threading.Thread(target=run, daemon=True).start()


def rects_hit(ax, ay, aw, ah, bx, by, bw, bh):
    return ax < bx + bw and ax + aw > bx and ay < by + bh and ay + ah > by


class BossFight:
    CX, CY = 176.0, 96.0
    RATE = dict(rain=80, aim=95, ring=170, spiral=250, trail=150, saw=260)

    def __init__(self, game, bid):
        self.g = game
        self.bid = bid
        sp = self.sp = BOSSES[bid]
        self.name = sp['name']
        self.maxhp = self.hp = sp['hp']
        self.w, self.h = sp['size']
        self.x, self.y = self.CX, -40.0
        self.t = 0
        self.state = 'intro'
        self.flash = 0
        self.projs = []
        self.cd = {}
        self.phase = 1
        self.shift_t = 420
        self.tele = None
        self.gi = 0
        self.seq = [DOWN, RIGHT, UP, LEFT]
        self.mv = 'idle'
        self.mt = 0
        self.vis = True
        self.spiral = 0
        self.ang = 0.0
        self.dead_t = 0
        self.dashdir = 1

    def box(self):
        return (self.x - self.w / 2.0, self.y - self.h / 2.0, self.w, self.h)

    # -- projectiles ------------------------------------------------------------
    def shoot(self, x, y, vx, vy, kind='bolt', r=3, life=400):
        if len(self.projs) < 90:
            self.projs.append(dict(x=x, y=y, vx=vx, vy=vy, r=r, life=life, kind=kind))

    def aim_at(self, spread=0.0, speed=2.2):
        s = self.g.sim
        dx = s.x + PS / 2 - self.x
        dy = s.y + PS / 2 - self.y
        a = math.atan2(dy, dx) + spread
        self.shoot(self.x, self.y, math.cos(a) * speed, math.sin(a) * speed)

    def fire(self, name):
        g, ph = self.g, self.phase
        sim = g.sim
        if name == 'rain':
            vx, vy = GVEC[sim.base]
            sp = 1.3 + 0.25 * ph
            for _ in range(2 + ph):
                if vx == 0:
                    y = 36 if vy > 0 else 156
                    self.shoot(random.uniform(40, 312), y, 0, vy * sp, 'rain', 3)
                else:
                    x = 34 if vx > 0 else 318
                    self.shoot(x, random.uniform(40, 152), vx * sp, 0, 'rain', 3)
        elif name == 'aim':
            if ph >= 2:
                for a in (-0.28, 0, 0.28):
                    self.aim_at(a, 2.1 + 0.2 * ph)
            else:
                self.aim_at(0, 2.2)
        elif name == 'ring':
            n = 8 + ph * 2
            off = random.uniform(0, 6.28)
            for i in range(n):
                a = off + i * 2 * math.pi / n
                self.shoot(self.x, self.y, math.cos(a) * 1.5, math.sin(a) * 1.5, 'ring', 3)
        elif name == 'spiral':
            self.spiral = 70
        elif name == 'trail':
            self.shoot(random.uniform(44, 308), 154, 0, 0, 'fire', 5, 150)
        elif name == 'saw':
            a = random.choice((0.7, 2.4, 3.9, 5.5))
            self.shoot(self.x, self.y, math.cos(a) * 2.2, math.sin(a) * 2.2, 'saw', 6, 420)

    # -- movement --------------------------------------------------------------------
    def move(self):
        t, m = self.t, self.sp['move']
        if m == 'mix':
            m = ('hover', 'orbit', 'pendulum')[(t // 600) % 3]
        if m == 'hover':
            self.x = self.CX + 78 * math.sin(t * 0.012)
            self.y = 62 + 16 * math.sin(t * 0.031)
        elif m == 'orbit':
            self.x = self.CX + 82 * math.cos(t * 0.015)
            self.y = 94 + 34 * math.sin(t * 0.015)
        elif m == 'pendulum':
            th = 0.95 * math.sin(t * 0.02)
            self.x = self.CX + 90 * math.sin(th)
            self.y = 36 + 88 * math.cos(th) * 0.85
        elif m == 'teleport':
            self.mt += 1
            if self.mv == 'idle' and self.mt >= 140:
                self.mv, self.mt, self.vis = 'blink', 0, False
            elif self.mv == 'blink' and self.mt >= 26:
                self.mv, self.mt, self.vis = 'idle', 0, True
                self.x, self.y = random.uniform(76, 276), random.uniform(56, 118)
                self.flash = 6
                self.fire('ring')
        elif m == 'charge':
            self.mt += 1
            floor_y = 160 - self.h / 2.0 - 1
            if self.mv == 'idle':
                self.x = self.CX + 64 * math.sin(self.t * 0.02)
                self.y += (64 - self.y) * 0.08
                if self.mt > 110:
                    self.mv, self.mt = 'tele', 0
                    self.dashdir = random.choice((-1, 1))
            elif self.mv == 'tele':
                tx = 68 if self.dashdir > 0 else 284
                self.x += (tx - self.x) * 0.12
                self.y += (floor_y - self.y) * 0.12
                if self.mt > 46:
                    self.mv, self.mt = 'dash', 0
            elif self.mv == 'dash':
                self.x += self.dashdir * (4.6 + 0.4 * self.phase)
                if self.mt % 7 == 0:
                    self.shoot(self.x, 154, 0, 0, 'fire', 5, 110)
                if self.x < 56 or self.x > 296:
                    self.mv, self.mt = 'back', 0
            else:
                self.x += (self.CX - self.x) * 0.05
                self.y += (64 - self.y) * 0.05
                if self.mt > 70:
                    self.mv, self.mt = 'idle', 0


    def update(self):
        g = self.g
        sim = g.sim
        self.t += 1
        if self.flash > 0:
            self.flash -= 1
        if self.state == 'intro':
            self.y += (64 - self.y) * 0.05
            if abs(self.y - 64) < 2:
                self.state = 'fight'
                self.t = 0
            return
        if self.state == 'dead':
            self.dead_t += 1
            if self.dead_t % 4 == 0:
                g.burst(self.x + random.uniform(-self.w / 2, self.w / 2), self.y + random.uniform(-self.h / 2, self.h / 2),
                        random.choice((C_GOLD, C_RED, '#ffffff')), 6, 2.2, 26)
                g.shake = 4
            self.projs = []
            if self.dead_t == 80:
                g.boss_defeated()
            return
        self.phase = 1 + (self.hp <= self.maxhp * 0.66) + (self.hp <= self.maxhp * 0.33)
        self.move()
        if self.vis:
            for name in self.sp['patterns'][self.phase - 1]:
                self.cd[name] = self.cd.get(name, 60) - 1
                if self.cd[name] <= 0:
                    self.fire(name)
                    self.cd[name] = int(self.RATE[name] * (1.15 - 0.1 * self.phase))
            if self.spiral > 0:
                self.spiral -= 1
                if self.spiral % 5 == 0:
                    self.ang += 0.5
                    self.shoot(self.x, self.y, math.cos(self.ang) * 1.6, math.sin(self.ang) * 1.6, 'ring', 3)
        # gravity shifts
        if self.sp.get('shift'):
            if self.tele:
                self.tele = (self.tele[0], self.tele[1] - 1)
                if self.tele[1] <= 0:
                    sim.base = self.tele[0]
                    g.sfx('field')
                    g.flash = 3
                    self.tele = None
                    self.shift_t = 520 - self.phase * 70
            else:
                self.shift_t -= 1
                if self.shift_t <= 0:
                    if 'cw' in self.sp['shift']:
                        self.gi = (self.gi + 1) % 4
                        d = self.seq[self.gi]
                    else:
                        names = {'right': RIGHT, 'left': LEFT, 'up': UP, 'down': DOWN}
                        opts = [names[n] for n in self.sp['shift']]
                        d = DOWN if sim.base != DOWN else random.choice(opts)
                    self.tele = (d, 70)
                    g.sfx('crystal_' + DNAME[d])
        self.update_projs()
        if self.vis and not sim.dead:
            bx, by, bw, bh = self.box()
            if rects_hit(sim.x, sim.y, PS, PS, bx + 3, by + 3, bw - 6, bh - 6):
                g.hurt(self.x, self.y)

    def update_projs(self):
        g = self.g
        sim = g.sim
        keep = []
        cx, cy = sim.x + PS / 2.0, sim.y + PS / 2.0
        for p in self.projs:
            p['life'] -= 1
            if p['life'] <= 0:
                continue
            nx, ny = p['x'] + p['vx'], p['y'] + p['vy']
            if p['kind'] == 'saw':
                if sim._solid(int(p['y'] // TILE), int(nx // TILE)):
                    p['vx'] = -p['vx']
                else:
                    p['x'] = nx
                if sim._solid(int(ny // TILE), int(p['x'] // TILE)):
                    p['vy'] = -p['vy']
                else:
                    p['y'] = ny
            else:
                p['x'], p['y'] = nx, ny
                if p['kind'] != 'fire' and sim._solid(int(ny // TILE), int(nx // TILE)):
                    continue
            if abs(p['x'] - cx) < PS / 2.0 + p['r'] - 1 and abs(p['y'] - cy) < PS / 2.0 + p['r'] - 1:
                g.hurt(p['x'], p['y'])
                if p['kind'] not in ('saw', 'fire'):
                    continue
            keep.append(p)
        self.projs = keep

    def hit(self, dmg):
        if self.state != 'fight' or not self.vis:
            return False
        self.hp -= dmg
        self.flash = 6
        self.g.sfx('soul')
        if self.hp <= 0:
            self.hp = 0
            self.state = 'dead'
            self.dead_t = 0
            self.g.sim.base = DOWN
            self.tele = None
            self.g.sfx('death')
        return True


def wrap_text(s, n):
    words, lines, cur = s.split(' '), [], ''
    for w in words:
        if len(cur) + len(w) + (1 if cur else 0) > n:
            lines.append(cur)
            cur = w
        else:
            cur = (cur + ' ' + w) if cur else w
    if cur:
        lines.append(cur)
    return lines


def story_new():
    return dict(started=True, flags=[], gears=[], pages=[], souls=0, souls_total=0, hearts=3, ab=[], buys={},
                cloaks=[0], loc='hub', collected={}, quests_done=[], deaths=0, frames=0, ended=False)


class StoryMixin:
    """story-mode behaviour mixed into the Game"""

    # -- state ------------------------------------------------------------------
    def story_init(self):
        self.script = None
        self.sp = 0
        self.say = None
        self.swait = 0
        self.sfade = 0.0
        self.sfade_to = 0.0
        self.sfade_rate = 0.0
        self.sbg = 'world'
        self.after = None
        self.boss = None
        self.bolts = []
        self.hp = 3
        self.atk_cd = 0
        self.loc = 'hub'
        self.near = None
        self.shop_i = 0
        self.jr_tab = 0
        self.jr_i = 0
        self.tv_i = 0
        self.wisp = [0.0, 0.0]
        self.credits_t = 0
        self.menu_msg = ''
        self.sm_i = 0

    @property
    def st(self):
        return self.save['story']

    def story_save(self):
        self.write_save()

    def maxhp(self):
        return self.st['hearts']

    def apply_abilities(self):
        self.sim.ab = set(a for a in self.st['ab'] if a in ('double', 'dash'))
        self.save['opts']['skin'] = self.save['opts']['skin'] if self.save['opts']['skin'] in self.st['cloaks'] else 0

    def has(self, a):
        return a in self.st['ab']

    def gears(self):
        return len(self.st['gears'])

    # -- level construction ------------------------------------------------------------
    def region_spec(self, rid):
        r = REGION[rid]
        return dict(name=r['name'], sub=r['sub'], theme=r['theme'], rooms=['START'] + r['rooms'] + ['END'],
                    seed=r['seed'], par=0, inv=r['inv'], hints=r['hints'], wisps=r['wisps'], saws=r['saws'])

    def story_enter(self, loc, arrive=None):
        st = self.st
        self.mode = 'story'
        self.loc = loc
        st['loc'] = loc
        boss_id = None
        
        # --- CRITICAL FIX: Force reset render overlays to clear the pitch black blank screen ---
        self.sfade = 0.0
        self.sfade_to = 0.0
        self.sfade_rate = 0.0
        self.script = None
        self.say = None
        # ---------------------------------------------------------------------------------------
        
        # --- CRITICAL FIX: Force reset render overlays to clear the pitch black blank screen ---
        self.sfade = 0.0
        self.sfade_to = 0.0
        self.sfade_rate = 0.0
        self.script = None
        self.say = None
        # ---------------------------------------------------------------------------------------
        
        if loc == 'hub':
            lvl = Level(HUB_SPEC)
        elif loc in REGION:
            lvl = Level(self.region_spec(loc))
            if loc != 'r7':
                idx = int(loc[1]) - 1
                pr = random.Random(REGION[loc]['seed'] + 5)
                for k, i in enumerate(pr.sample(range(len(lvl.souls)), 2)):
                    lvl.souls[i]['page'] = idx * 2 + k
        else:
            boss_id = REGION['r' + loc[1:]]['boss']
            lvl = GridLevel(arena_data(boss_id))
            
        self.lvl = lvl
        self.sim = Sim(lvl)
        self.apply_abilities()
        self.stats = dict(frames=0, deaths=0, souls=0)
        self.particles, self.bolts = [], []
        self.toast = None
        self.shake = self.flash = self.dead_t = 0
        self.spring_anim = {}
        self.boss = None
        self.near = None
        self.hp = self.maxhp()
        
        for i, s in enumerate(lvl.souls):
            if st['collected'].get('%s:%d' % (loc, i)):
                self.sim.souls[i] = True
                
        if loc == 'hub' and arrive:
            ent = [e for e in lvl.ents if e.get('to') == arrive]
            if ent:
                self.sim.reset_player(ent[0]['x'] + 2, (ent[0]['r'] + 1) * TILE - PS)
                self.sim.respawn = (self.sim.x, self.sim.y)
                
        self.sim.inv = 40
        self.cam_snap()
        self.wisp = [self.sim.x, self.sim.y - 14]
        self.state = 'play'
        
        if loc == 'hub':
            self.bgm('s_hub', 5, 'hub')
        elif loc in REGION:
            self.bgm('w%d' % lvl.theme, lvl.theme * 7 + 3, THEMES[lvl.theme]['mood'])
        else:
            bid = boss_id
            self.boss = BossFight(self, bid)
            self.bgm('boss_' + bid, int(bid[1]) * 5, 'finale' if bid == 'b7' else 'boss')
            self.start_script((FINAL_PRE if bid == 'b7' else []) + BOSS_INTRO[bid])
            
        self.story_save()

    def story_new_game(self):
        self.save['story'] = story_new()
        self.story_save()
        self.story_enter('hub')
        self.start_script(script_prologue())

    def story_continue(self):
        if not self.save['story'].get('started'):
            return self.story_new_game()
        loc = self.st['loc']
        if loc not in ('hub',) and loc not in REGION and not loc.startswith('a'):
            loc = 'hub'
        if loc.startswith('a'):
            loc = 'hub'
        self.story_enter(loc)

    # -- cutscenes -----------------------------------------------------------------------
    def start_script(self, cmds, after=None):
        self.script = list(cmds)
        self.sp = 0
        self.say = None
        self.swait = 0
        self.after = after
        self.sbg = 'world'

    def end_script(self):
        self.script = None
        self.say = None
        cb, self.after = self.after, None
        if cb:
            cb()

    def run_script(self):
        ev = self.events
        if self.sfade != self.sfade_to:
            d = self.sfade_rate
            self.sfade = min(self.sfade_to, self.sfade + d) if self.sfade_to > self.sfade else max(self.sfade_to, self.sfade - d)
            return
        if self.say:
            s = self.say
            s['n'] += 1.4
            full = len(s['text'])
            if self.pressed(K_OK) or 'e' in ev:
                if s['n'] < full:
                    s['n'] = full
                else:
                    self.say = None
            elif int(s['n']) <= full and int(s['n']) % 3 == 0 and s['who'] != '' and int(s['n']) != s.get('last'):
                s['last'] = int(s['n'])
                self.sfx('menu')
            return
        if self.swait > 0:
            self.swait -= 1
            return
        if self.sp >= len(self.script):
            self.end_script()
            return
        c = self.script[self.sp]
        self.sp += 1
        k, st = c[0], self.st
        if k == 'say':
            self.say = dict(who=c[1], text=c[2], n=0.0)
        elif k == 'wait':
            self.swait = c[1]
        elif k == 'fade_out':
            self.sfade_to, self.sfade_rate = 1.0, 1.0 / c[1]
        elif k == 'fade_in':
            self.sfade = 1.0        # Double-check that it starts at max opacity
            self.sfade_to = 0.0     # And targets transparency
            self.sfade_rate = 1.0 / float(c[1]) # Ensure floating division values map properly
        elif k == 'bg':
            self.sbg = c[1]
        elif k == 'shake':
            self.shake = c[1]
        elif k == 'sfx':
            self.sfx(c[1])
        elif k == 'flag':
            if c[1] not in st['flags']:
                st['flags'].append(c[1])
            self.story_save()
        elif k == 'give':
            if c[1] == 'lantern':
                if 'lantern' not in st['ab']:
                    st['ab'].append('lantern')
                if 'got_lantern' not in st['flags']:
                    st['flags'].append('got_lantern')
                self.toast = ['GOT THE SOUL LANTERN! PRESS X', 240]
            self.story_save()
        elif k == 'gear':
            bid = c[1]
            rid = [r for r in REGIONS if r['boss'] == bid][0]['id']
            if rid not in st['gears']:
                st['gears'].append(rid)
            self.toast = ['GOT THE %s' % BOSSES[bid]['gear'], 260]
            self.sfx('clear')
            self.story_save()
        elif k == 'souls':
            st['souls'] += c[1]
            st['souls_total'] += c[1]
            self.story_save()
        elif k == 'quests':
            self.start_quest_check()
        elif k == 'shop':
            self.shop_i = 0
            self.state = 'shop'
        elif k == 'warp':
            tgt = c[1]
            self.script = None
            self.goto(lambda t=tgt: self.story_enter(*(t.split(':') if ':' in t else (t,))))
        elif k == 'ending':
            self.start_script(ENDING)
        elif k == 'credits':
            self.script = None
            self.credits_t = 0
            self.state = 'credits'
        elif k == 'heal':
            self.hp = self.maxhp()
        elif k == 'music':
            self.bgm(c[1], c[2], c[3])

    def start_quest_check(self):
        st = self.st
        who = self.say['who'] if self.say else ''
        lines = []
        # look at the last speaker in the script history
        sp = [x for x in self.script[:self.sp] if x[0] == 'say']
        who = sp[-1][1] if sp else ''
        stats = dict(souls_total=st['souls_total'], pages=len(st['pages']), gears=len(st['gears']))
        pending = []
        for q in QUESTS:
            if q['who'] != who or q['id'] in st['quests_done']:
                continue
            if stats[q['stat']] >= q['goal']:
                st['quests_done'].append(q['id'])
                kind, n = q['reward']
                if kind == 'souls':
                    st['souls'] += n
                    st['souls_total'] += n
                    lines.append(sc(who, '"%s" COMPLETE! HERE ARE %d SOULS.' % (q['title'], n)))
                else:
                    st['hearts'] += n
                    self.hp = self.maxhp()
                    lines.append(sc(who, '"%s" COMPLETE! HAVE A HEART CONTAINER.' % q['title']))
                lines.append(('sfx', 'clear'))
            else:
                pending.append(q)
        if not lines and pending:
            q = pending[0]
            lines.append(sc(who, 'NEXT: %s (%d/%d)' % (q['desc'], stats[q['stat']], q['goal'])))
        self.script[self.sp:self.sp] = lines
        self.story_save()

    # -- hooks into the play loop -----------------------------------------------------------------
    def pre_step(self):
        if self.mode != 'story':
            return False
        if self.script is not None:
            self.run_script()
            return True
        return False

    def dash_key(self):
        return self.mode == 'story' and self.pressed({'shift_l', 'shift_r', 'c'})

    def post_step(self, ev):
        if self.mode != 'story':
            return
        sim, lvl, st = self.sim, self.lvl, self.st
        cx, cy = sim.x + PS / 2.0, sim.y + PS / 2.0
        for e in ev:
            if e in ('dash', 'jump2'):
                self.sfx('jump')
                self.burst(cx, cy, '#8ff7ff', 6, 1.2, 14)
            elif isinstance(e, tuple) and e[0] == 'cp':
                self.hp = self.maxhp()
                self.toast = ['REST. HEARTS RESTORED', 100]
        st['frames'] += 1
        self.atk_cd = max(0, self.atk_cd - 1)
        # lantern bolts
        if self.has('lantern') and self.atk_cd <= 0 and self.pressed({'x', 'j', 'f'}):
            g = sim.eff
            if g < 2:
                lat = (1, 0)
                face = sim.face
                dirv = (face, 0)
                away = (0, -GVEC[g][1])
            else:
                dirv = (0, sim.face)
                away = (-GVEC[g][0], 0)
            ak = {'w', 'up'} if g == DOWN else ({'s', 'down'} if g == UP else ({'d', 'right'} if g == LEFT else {'a', 'left'}))
            v = away if self.held & ak else dirv
            if self.boss and self.boss.state == 'fight' and self.boss.vis:
                ax, ay = self.boss.x - cx, self.boss.y - cy
                dd = math.hypot(ax, ay) or 1.0
                v = (ax / dd, ay / dd)
            dmg = 2 if self.has('lantern2') else 1
            self.bolts.append(dict(x=cx + v[0] * 7, y=cy + v[1] * 7, vx=v[0] * 4.6, vy=v[1] * 4.6, life=70, d=dmg))
            self.atk_cd = 16
            self.sfx('jump')
        nb = []
        for b in self.bolts:
            b['x'] += b['vx']
            b['y'] += b['vy']
            b['life'] -= 1
            if b['life'] <= 0 or sim._solid(int(b['y'] // TILE), int(b['x'] // TILE)):
                self.burst(b['x'], b['y'], C_CYAN, 3, 0.8, 10)
                continue
            if self.boss and self.boss.state == 'fight' and self.boss.vis:
                bx, by, bw, bh = self.boss.box()
                if rects_hit(b['x'] - 2, b['y'] - 2, 4, 4, bx, by, bw, bh):
                    if self.boss.hit(b['d']):
                        self.burst(b['x'], b['y'], C_GOLD, 6, 1.6, 16)
                        continue
            nb.append(b)
        self.bolts = nb
        if self.boss:
            self.boss.update()
        # magnet
        if self.has('magnet'):
            for i, s in enumerate(lvl.souls):
                if not sim.souls[i]:
                    dx, dy = lvl.wd(cx - (s['x'] + 4)), cy - (s['y'] + 4)
                    d = math.hypot(dx, dy)
                    if 0 < d < 52:
                        s['x'] += dx / d * 1.6
                        s['y'] += dy / d * 1.6
        # interaction
        self.near = None
        if self.boss is None:
            for e in lvl.ents:
                if abs(lvl.wd(e['x'] + 8 - cx)) < 15 and abs(e['y'] + 8 - cy) < 20:
                    self.near = e
                    break
            if self.near and (self.pressed({'e', 'return'})):
                self.interact(self.near)
        # wisp companion
        self.wisp[0] += lvl.wd(cx - 12 - self.wisp[0]) * 0.07
        self.wisp[1] += (cy - 16 + math.sin(self.t * 0.07) * 3 - self.wisp[1]) * 0.07

    def gate_locked(self, rid):
        st = self.st
        if 'got_lantern' not in st['flags']:
            return 'SEE MIRA FIRST'
        need = REGION[rid]['need']
        if self.gears() < need:
            return 'NEEDS %d GEARS' % need
        return None

    def interact(self, e):
        t = e['t']
        st = self.st
        if t == 'npc':
            who = e['id']
            if who == 'mira':
                if 'met_mira' not in st['flags']:
                    self.start_script(script_mira_intro())
                else:
                    self.start_script([sc('MIRA', 'BACK FOR MORE? GOOD. SOULS BUY THINGS. THINGS KEEP YOU ALIVE.'), ('shop',)])
            elif who == 'brin':
                self.start_script(script_brin(st))
            elif who == 'tock':
                self.start_script(script_tock(st))
            elif who == 'cog':
                self.start_script(script_cog(st))
            elif who == 'bellows':
                self.start_script(script_bellows(st))
            elif who == 'ghost':
                self.start_script(script_ghost(st))
        elif t == 'warp':
            why = self.gate_locked(e['to'])
            if why:
                self.sfx('back')
                self.toast = ['SEALED: ' + why, 120]
            else:
                rid = e['to']
                self.sfx('ok')
                self.goto(lambda r=rid: self.story_enter(r))
        elif t == 'lift':
            self.tv_i = 0
            self.state = 'travel'

    def hurt(self, sx, sy):
        sim = self.sim
        if sim.inv > 0 or sim.dead or self.dead_t > 0:
            return
        self.hp -= 1
        sim.inv = 100
        self.flash = 4
        if self.save['opts']['shake']:
            self.shake = 8
        self.sfx('reset')
        self.burst(sim.x + PS / 2, sim.y + PS / 2, C_RED, 10, 2.0, 18)
        dx = sim.x + PS / 2 - sx
        dy = sim.y + PS / 2 - sy
        d = math.hypot(dx, dy) or 1.0
        sim.vx += dx / d * 3.0
        sim.vy += dy / d * 3.0
        if self.hp <= 0:
            self.on_death()

    def respawn_hook(self):
        if self.mode == 'story' and self.loc.startswith('a'):
            loc = self.loc
            self.story_enter(loc)
            self.script = None
            if self.boss:
                self.boss.state = 'intro'
            self.sim.inv = 60
            return True
        if self.mode == 'story':
            self.hp = self.maxhp()
        return False

    def boss_defeated(self):
        st = self.st
        bid = self.boss.bid
        rid = next(r['id'] for r in REGIONS if r['boss'] == bid)
        
        # Clear out hazardous tracking states immediately to prevent background collision loops
        self.bolts = []
        self.particles = []
        
        st['souls'] += BOSSES[bid]['reward']
        st['souls_total'] += BOSSES[bid]['reward']
        if bid not in st.setdefault('bosses', []):
            st['bosses'].append(bid)
            
        self.toast = ['+%d SOULS' % BOSSES[bid]['reward'], 150]
        self.hp = self.maxhp()
        
        # Build out the robust outro script pipeline
        cmds = list(BOSS_OUTRO[bid])
        if bid != 'b7':
            cmds += [('wait', 20), ('fade_out', 30), ('warp', 'hub:' + rid)]
            
        # Nuke the boss entity instance completely BEFORE processing scripts
        self.boss = None 
        
        # Reset safe system variables for player survival tracking
        self.sim.dead = False
        self.dead_t = 0
        self.sim.inv = 200  # Give long invulnerability frames to guarantee safety
        
        # Trigger the cutscene state engine
        self.start_script(cmds)
        self.story_save()

    def story_soul_events(self, ev):
        st, lvl = self.st, self.lvl
        for e in ev:
            if isinstance(e, tuple) and e[0] == 'soul':
                i = e[1]
                st['collected']['%s:%d' % (self.loc, i)] = True
                s = lvl.souls[i]
                if s.get('page') is not None:
                    pid = s['page']
                    if pid not in st['pages']:
                        st['pages'].append(pid)
                    title, body = PAGES[pid]
                    self.sfx('clear')
                    self.start_script([('sfx', 'check'), sc('', 'JOURNAL PAGE: ' + title + '. ' + body)])
                else:
                    st['souls'] += 1
                    st['souls_total'] += 1
        if ev:
            self.story_save() if any(isinstance(e, tuple) and e[0] == 'soul' for e in ev) else None

    # -- shop / journal / travel / credits states ------------------------------------------------------------
    def shop_price(self, key):
        for (k, name, desc, prices) in SHOP:
            if k == key:
                n = self.st['buys'].get(k, 0)
                return prices[n] if n < len(prices) else None
        return None

    def shop_buy(self, key):
        st = self.st
        price = self.shop_price(key)
        if price is None or st['souls'] < price:
            self.sfx('back')
            return False
        st['souls'] -= price
        st['buys'][key] = st['buys'].get(key, 0) + 1
        if key == 'heart':
            st['hearts'] += 1
            self.hp = self.maxhp()
        elif key.startswith('cloak'):
            n = int(key[5:])
            if n not in st['cloaks']:
                st['cloaks'].append(n)
            self.save['opts']['skin'] = n
        else:
            if key == 'lantern2' or key in ('double', 'dash', 'magnet'):
                if key not in st['ab']:
                    st['ab'].append(key)
            self.apply_abilities()
        self.sfx('clear')
        self.story_save()
        return True

    def upd_shop(self):
        n = len(SHOP)
        if self.pressed(K_UPK):
            self.shop_i = (self.shop_i - 1) % n
            self.sfx('menu')
        if self.pressed(K_DOWNK):
            self.shop_i = (self.shop_i + 1) % n
            self.sfx('menu')
        if self.pressed(K_OK):
            self.shop_buy(SHOP[self.shop_i][0])
        if self.pressed(K_BACK):
            self.state = 'play'

    def upd_travel(self):
        tiers = self.hub_tiers()
        if self.pressed(K_UPK):
            self.tv_i = (self.tv_i - 1) % len(tiers)
        if self.pressed(K_DOWNK):
            self.tv_i = (self.tv_i + 1) % len(tiers)
        if self.pressed(K_BACK):
            self.state = 'play'
        elif self.pressed(K_OK):
            e = tiers[self.tv_i]
            self.sim.reset_player(e['x'] + 4, (e['r'] + 1) * TILE - PS)
            self.sim.respawn = (self.sim.x, self.sim.y)
            self.cam_snap()
            self.state = 'play'
            self.sfx('field')

    def hub_tiers(self):
        rows = {}
        for e in self.lvl.ents:
            rows.setdefault(e['r'], e)
        return [rows[r] for r in sorted(rows, reverse=True)]

    def upd_journal(self):
        if self.pressed(K_LEFTK):
            self.jr_tab = (self.jr_tab - 1) % 3
            self.jr_i = 0
        if self.pressed(K_RIGHTK):
            self.jr_tab = (self.jr_tab + 1) % 3
            self.jr_i = 0
        if self.pressed(K_UPK):
            self.jr_i = max(0, self.jr_i - 1)
        if self.pressed(K_DOWNK):
            self.jr_i += 1
        if self.pressed(K_BACK) or self.pressed({'e'}):
            self.state = 'play'

    def upd_credits(self):
        self.credits_t += 1
        if self.pressed(K_BACK) or self.credits_t > 60 * 22:
            self.st['ended'] = True
            self.story_save()
            self.goto(lambda: self.story_enter('hub'))


# ============================================================================
#  GAME  (screens, input, rendering)
# ============================================================================
class _EditSim:
    """stand-in for Sim when only drawing a level (editor / previews)"""

    def __init__(self, lvl, t):
        self.gone, self.crumb = {}, {}
        self.lit = [False] * len(lvl.cps)
        self.souls = [False] * len(lvl.souls)
        self.t = t
        self.inv = 0


RINGS = [(62, 22, 1.0), (84, 30, -1.0), (106, 40, 0.6)]
SPIKE_DIR = {2: UP, 3: DOWN, 4: LEFT, 5: RIGHT}

DEFAULT_SAVE = dict(unlocked=1, best={}, opts=dict(music=6, sfx=8, shake=True, skin=0),
                    endless=dict(score=0, sections=0), daily={}, stats=dict(deaths=0, souls=0, frames=0))


def fmt_time(s):
    return '%d:%02d' % (int(s) // 60, int(s) % 60)


class Game:
    def __init__(self, root, windowed=False, mute=False):
        self.root = root
        self.windowed = windowed
        self.running = True  # <-- Initialize running here before any bgm() calls
        self.canvas = DrawCanvas(root)
        self.canvas.pack(fill='both', expand=True)
        root.update()
        w, h = root.winfo_width(), root.winfo_height()
        if w < 300 or h < 200:
            w, h = root.winfo_screenwidth(), root.winfo_screenheight()
        self.S = 0
        self.assets = None
        self.apply_size(w, h)

        self.held, self.rel, self.events = set(), {}, []
        self.chars = []
        self.t = 0
        self.state = 'title'
        self.menu = 0
        self.trans = None
        self.save = self.load_save()
        self.audio = AudioX(mute)
        self.audio.mvol = self.save['opts']['music']
        self.audio.svol = self.save['opts']['sfx']
        self.mode = 'campaign'
        self.lvl = None
        self.sim = None
        self.li = 0
        self.endless = None
        self.eseed = 1
        self.stats = dict(frames=0, deaths=0, souls=0)
        self.particles = []
        self.shake = 0
        self.flash = 0
        self.dead_t = 0
        self.toast = None
        self.camx = self.camy = 0.0
        self.intro_t = 0
        self.result = None
        self.sel = 0
        self.spring_anim = {}
        self.unlock_msg = None
        self.run_tot = dict(frames=0, deaths=0, souls=0)
        rnd = random.Random(3)
        self.embers = [[rnd.uniform(0, 600), rnd.uniform(0, 400), rnd.uniform(0.15, 0.5),
                        rnd.uniform(0, 6.28), rnd.randrange(3)] for _ in range(34)]
        self.stars = [(rnd.random(), rnd.random() * 0.8, rnd.uniform(0, 6.28)) for _ in range(60)]
        self.bgm('title', 1, 'title')

        root.bind('<KeyPress>', self.on_down)
        root.bind('<KeyRelease>', self.on_up)
        self.canvas.bind('<Configure>', self.on_configure)
        root.protocol('WM_DELETE_WINDOW', self.quit)
        root.focus_force()
        self.post_init()
        self.last = time.perf_counter()
        self.acc = 0.0
        self.loop()

    def post_init(self):
        pass

    # -- sizing / save ------------------------------------------------------
    def apply_size(self, w, h):
        S = max(2, int(round(min(w / 320.0, h / 180.0))))
        self.sw, self.sh = w, h
        self.VW, self.VH = w / float(S), h / float(S)
        if S != self.S:
            self.S = S
            self.assets = AssetsX(S)

    def on_configure(self, ev):
        if ev.width > 200 and ev.height > 150 and (ev.width != self.sw or ev.height != self.sh):
            self.apply_size(ev.width, ev.height)

    def load_save(self):
        d = json.loads(json.dumps(DEFAULT_SAVE))
        try:
            with open(SAVE_PATH, 'r') as f:
                s = json.load(f)
            for k, v in s.items():
                if isinstance(v, dict) and isinstance(d.get(k), dict):
                    d[k].update(v)
                else:
                    d[k] = v
        except Exception:
            pass
        return d

    def write_save(self):
        try:
            with open(SAVE_PATH, 'w') as f:
                json.dump(self.save, f)
        except Exception:
            pass

    def total_stars(self):
        return sum(b.get('stars', 0) for b in self.save['best'].values())

    def skin_ok(self, i):
        return self.total_stars() >= SKINS[i][1]

    def sfx(self, name):
        self.audio.play(name)

    # -- input --------------------------------------------------------------
    def is_typing(self):
        """True while any text box (editor, music maker, portal search) is open."""
        ed = getattr(self, 'editor', None)
        mm = getattr(self, 'mm', None)
        return bool((ed is not None and getattr(ed, 'edit', None))
                    or (mm is not None and getattr(mm, 'edit', None))
                    or getattr(self, 'portal_edit', None) is not None)

    def on_down(self, e):
        k = e.keysym.lower()
        typing = self.is_typing()
        ch = getattr(e, 'char', '') or ''
        if typing and len(ch) == 1 and ch.isprintable():
            self.chars.append(ch)
        if k == 'f11':
            self.toggle_fullscreen()
            return
        if k == 'm' and not typing:
            self.audio.muted = not self.audio.muted
            self.audio.set_volumes()
            return
        if k in self.rel:
            del self.rel[k]
            self.held.add(k)
            return
        if k not in self.held:
            self.held.add(k)
            self.events.append(k)

    def on_up(self, e):
        self.rel[e.keysym.lower()] = time.perf_counter()

    def flush_releases(self):
        now = time.perf_counter()
        for k in list(self.rel):
            if now - self.rel[k] > 0.04:
                del self.rel[k]
                self.held.discard(k)

    def down(self, keys):
        return bool(self.held & keys)

    def pressed(self, keys):
        return any(k in keys for k in self.events)

    def toggle_fullscreen(self):
        try:
            cur = bool(self.root.attributes('-fullscreen'))
            self.root.attributes('-fullscreen', not cur)
        except Exception:
            pass

    def quit(self):
        self.save['stats']['frames'] += 0
        self.write_save()
        self.audio.shutdown()
        self.root.destroy()

    def read_input(self):
        g = self.sim.eff
        L_, R_ = self.down(K_LEFTK), self.down(K_RIGHTK)
        U_, D_ = self.down(K_UPK), self.down(K_DOWNK)
        if g in (DOWN, UP):
            lat = (1 if R_ else 0) - (1 if L_ else 0)
            away = U_ if g == DOWN else D_
            aev = self.pressed(K_UPK) if g == DOWN else self.pressed(K_DOWNK)
        else:
            lat = (1 if D_ else 0) - (1 if U_ else 0)
            away = R_ if g == LEFT else L_
            aev = self.pressed(K_RIGHTK) if g == LEFT else self.pressed(K_LEFTK)
        return lat, self.pressed(K_JUMPK) or aev, self.down(K_JUMPK) or away

    # -- drawing helpers ----------------------------------------------------
    def rect(self, x, y, w, h, col):
        S = self.S
        self.canvas.create_rectangle(int(round(x * S)), int(round(y * S)),
                                     int(round((x + w) * S)), int(round((y + h) * S)),
                                     fill=col, outline='')

    def img(self, im, x, y):
        self.canvas.create_image(int(round(x * self.S)), int(round(y * self.S)),
                                 image=im, anchor='nw')

    def text(self, s, x, y, col=C_TEXT, size=1, align='l', shadow=True):
        s = str(s).upper()
        if not s:
            return 0
        w = len(s) * 4 * size - size
        if align == 'c':
            x -= w / 2.0
        elif align == 'r':
            x -= w
        if shadow:
            self.img(self.assets.text(s, '#000000', size), x + 1, y + 1)
        self.img(self.assets.text(s, col, size), x, y)
        return w

    def wave_text(self, s, cx, y, size, col, amp, speed, shadow='#2a1450'):
        total = len(s) * 4 * size - size
        x = cx - total / 2.0
        for i, ch in enumerate(s):
            if ch != ' ':
                yo = amp * math.sin(self.t * speed + i * 0.55)
                self.img(self.assets.text(ch, shadow, size), x + 1, y + yo + 1)
                self.img(self.assets.text(ch, col, size), x, y + yo)
            x += 4 * size

    def panel(self, x, y, w, h):
        self.rect(x - 1, y - 1, w + 2, h + 2, C_EDGE)
        self.rect(x, y, w, h, C_PANEL)

    # -- flow ---------------------------------------------------------------
    def goto(self, fn):
        if self.trans is None:
            self.trans = dict(ph=0, t=0, cb=fn)

    def set_state(self, st):
        self.state = st
        self.menu = 0

    def go_title(self):
        self.bgm('title', 1, 'title')
        self.set_state('title')

    def begin_level(self, spec):
        self.lvl = self.make_level(spec)
        self.sim = Sim(self.lvl)
        self.stats = dict(frames=0, deaths=0, souls=0)
        self.particles = []
        self.toast = None
        self.shake = self.flash = self.dead_t = 0
        self.spring_anim = {}
        self.sim.inv = 40
        self.cam_snap()
        self.state = 'intro'
        self.intro_t = 0
        th = THEMES[self.lvl.theme]
        if self.mode == 'endless':
            self.bgm('e%d' % (self.endless['section'] % 5), self.eseed % 50 + self.endless['section'] % 5, 'endless')
        else:
            self.bgm('w%d' % self.lvl.theme, self.lvl.theme * 7 + 3, th['mood'])

    def make_level(self, spec):
        return Level(spec)

    def bgm(self, key, seed, mood):
        self.audio.music(key, seed, mood)

    def start_campaign(self, i):
        self.mode = 'campaign'
        self.li = i
        self.begin_level(LEVELS[i])

    def start_endless(self):
        self.mode = 'endless'
        self.eseed = random.randrange(1, 10 ** 6)
        self.endless = dict(section=1, lives=5, score=0, souls=0, floors=0, nextlife=25)
        self.begin_level(procedural_spec(self.eseed, 1))

    def start_daily(self):
        self.mode = 'daily'
        seed = int(time.strftime('%Y%m%d'))
        spec = procedural_spec(seed, 4, rooms_n=7, diff=3.0, name='DAILY TOWER',
                               theme=seed % len(THEMES), inv=(seed % 3 == 0))
        spec['par'] = 200
        spec['hints'] = False
        self.daily_key = str(seed)
        self.begin_level(spec)

    def cam_snap(self):
        s = self.sim
        self.camx = s.x + PS / 2.0
        if not self.lvl.ring:
            lo, hi = self.VW / 2.0, self.lvl.wpx - self.VW / 2.0
            self.camx = self.lvl.wpx / 2.0 if hi < lo else max(lo, min(hi, self.camx))
        self.camy = self.clamp_cam(s.y + PS / 2.0)

    def clamp_cam(self, y):
        lo = self.VH / 2.0
        hi = self.lvl.hpx - self.VH / 2.0
        if hi < lo:
            return self.lvl.hpx / 2.0
        return max(lo, min(hi, y))

    # -- main loop ----------------------------------------------------------
    def loop(self):
        t0 = time.perf_counter()
        self.acc += min(t0 - self.last, 0.1)
        self.last = t0
        n = 0
        while self.acc >= DT and n < 4:
            self.flush_releases()
            self.update()
            self.events = []
            self.acc -= DT
            n += 1
        self.audio.tick()
        self.render()
        ms = (time.perf_counter() - t0) * 1000.0
        self.canvas.flush()
        self.root.after(1, self.loop)

    # ======================================================================
    #  UPDATE
    # ======================================================================

    def update(self):
        self.t += 1
        if self.trans:
            tr = self.trans
            tr['t'] += 1
            if tr['ph'] == 0 and tr['t'] >= 14:
                tr['cb']()
                tr['ph'] = 1
                tr['t'] = 0
            elif tr['ph'] == 1 and tr['t'] >= 14:
                self.trans = None
            self.events = []
            if self.state != 'play':
                return
        fn = getattr(self, 'upd_' + self.state, None)
        if fn:
            fn()

    def menu_nav(self, n):
        if self.pressed(K_UPK):
            self.menu = (self.menu - 1) % n
            self.sfx('menu')
        if self.pressed(K_DOWNK):
            self.menu = (self.menu + 1) % n
            self.sfx('menu')

    def title_items(self):
        first = 'PLAY' if self.save['unlocked'] <= 1 and not self.save['best'] else 'CONTINUE'
        return [first, 'LEVEL SELECT', 'ENDLESS TOWER', 'DAILY TOWER', 'OPTIONS',
                'HOW TO PLAY', 'QUIT']

    def upd_title(self):
        self.menu_nav(len(TITLE_ITEMS))
        if self.pressed(K_OK):
            self.sfx('ok')
            m = self.menu
            it = TITLE_ITEMS[m]
            
            if it == 'LEVEL PORTAL':
                import webbrowser
                open_url('https://ttt-level-portal.on.websim.com')
                self.toast = ['PORTAL OPENED IN BROWSER', 120]
            elif it == 'STORY MODE':
                self.goto(lambda: (self.set_state('story_menu'), setattr(self, 'menu_msg', '')))
            elif it == 'CAMPAIGN':
                i = min(self.save['unlocked'], len(LEVELS)) - 1
                self.run_tot = dict(frames=0, deaths=0, souls=0)
                self.goto(lambda: self.start_campaign(max(0, i)))
            elif it == 'LEVEL SELECT':
                self.goto(lambda: (self.set_state('select'), setattr(self, 'sel', 0)))
            elif it == 'ENDLESS TOWER':
                self.goto(self.start_endless)
            elif it == 'DAILY TOWER':
                self.goto(self.start_daily)
            elif it == 'LEVEL EDITOR':
                self.goto(lambda: self.open_editor())
            elif it == 'MY LEVELS':
                self.goto(self.open_custom)
            elif it == 'MUSIC MAKER':
                self.goto(self.open_music)
            elif it == 'OPTIONS':
                self.goto(lambda: self.set_state('options'))
            elif it == 'HOW TO PLAY':
                self.goto(lambda: self.set_state('howto'))
            elif it == 'QUIT':
                self.quit()

    def upd_howto(self):
        if self.pressed(K_OK) or self.pressed(K_BACK):
            self.sfx('back')
            self.goto(self.go_title)

    def upd_options(self):
        o = self.save['opts']
        self.menu_nav(5)
        step = (1 if self.pressed(K_RIGHTK) else 0) - (1 if self.pressed(K_LEFTK) else 0)
        m = self.menu
        changed = False
        if step or self.pressed(K_OK):
            if m == 0:
                o['music'] = max(0, min(10, o['music'] + (step or 1)))
                self.audio.mvol = o['music']
                self.audio.set_volumes()
                changed = True
            elif m == 1:
                o['sfx'] = max(0, min(10, o['sfx'] + (step or 1)))
                self.audio.svol = o['sfx']
                changed = True
            elif m == 2:
                o['shake'] = not o['shake']
                changed = True
            elif m == 3:
                n = len(SKINS)
                for k in range(1, n + 1):
                    c = (o['skin'] + (step or 1) * k) % n
                    if self.skin_ok(c):
                        o['skin'] = c
                        break
                changed = True
            elif m == 4 and self.pressed(K_OK):
                self.write_save()
                self.goto(self.go_title)
                self.sfx('back')
                return
            if changed:
                self.sfx('ok')
        if self.pressed(K_BACK):
            self.write_save()
            self.sfx('back')
            self.goto(self.go_title)

    def upd_select(self):
        n = len(LEVELS)
        if self.pressed(K_UPK):
            self.sel = (self.sel - 1) % n
            self.sfx('menu')
        if self.pressed(K_DOWNK):
            self.sel = (self.sel + 1) % n
            self.sfx('menu')
        if self.pressed(K_BACK):
            self.sfx('back')
            self.goto(self.go_title)
        elif self.pressed(K_OK):
            if self.sel < self.save['unlocked']:
                self.sfx('ok')
                i = self.sel
                self.run_tot = dict(frames=0, deaths=0, souls=0)
                self.goto(lambda: self.start_campaign(i))

    def upd_intro(self):
        self.intro_t += 1
        if self.intro_t > 20 and (self.pressed(K_OK) or self.intro_t > 140):
            self.goto(lambda: setattr(self, 'state', 'play'))
        elif self.pressed(K_BACK):
            self.goto(self.go_title)

    def pause_items(self):
        return ['RESUME', 'RESTART FLOOR', 'SOUND: ' + ('OFF' if self.audio.muted else 'ON'),
                'QUIT TO TITLE']

    def upd_pause(self):
        self.menu_nav(4)
        if self.pressed(K_BACK):
            self.state = 'play'
            return
        if self.pressed(K_OK):
            self.sfx('ok')
            m = self.menu
            if m == 0:
                self.state = 'play'
            elif m == 1:
                spec = self.lvl.spec
                self.goto(lambda: self.begin_level(spec))
            elif m == 2:
                self.audio.muted = not self.audio.muted
                self.audio.set_volumes()
            else:
                self.goto(self.go_title)

    def upd_clear(self):
        if self.pressed(K_OK):
            self.sfx('ok')
            if self.mode == 'campaign':
                nxt = self.li + 1
                if nxt >= len(LEVELS):
                    self.goto(lambda: self.set_state('ending'))
                else:
                    self.goto(lambda: self.start_campaign(nxt))
            elif self.mode == 'endless':
                self.endless['section'] += 1
                sec = self.endless['section']
                self.goto(lambda: self.begin_level(procedural_spec(self.eseed, sec)))
            else:
                self.goto(self.go_title)
        elif self.pressed(K_BACK):
            self.goto(self.go_title)

    def upd_ending(self):
        if self.pressed(K_OK) or self.pressed(K_BACK):
            self.goto(self.go_title)

    def upd_gameover(self):
        if self.pressed(K_OK) or self.pressed(K_BACK):
            self.sfx('ok')
            self.goto(self.go_title)

    # -- gameplay -----------------------------------------------------------
    def burst(self, x, y, col, n, speed=1.6, life=26, size=1.0):
        for _ in range(n):
            a = random.uniform(0, math.pi * 2)
            s = random.uniform(0.3, speed)
            self.particles.append([x, y, math.cos(a) * s, math.sin(a) * s - 0.2,
                                   life + random.randint(-6, 6), col, size])

    def upd_play(self):
        sim, lvl = self.sim, self.lvl
        if self.pressed(K_BACK) or 'p' in self.events:
            self.state = 'pause'
            self.menu = 0
            return
        if self.pre_step():
            self.update_fx()
            self.update_camera()
            return
        self.stats['frames'] += 1
        if self.shake > 0:
            self.shake -= 1
        if self.flash > 0:
            self.flash -= 1
        if self.toast:
            self.toast[1] -= 1
            if self.toast[1] <= 0:
                self.toast = None
        for k in list(self.spring_anim):
            self.spring_anim[k] -= 1
            if self.spring_anim[k] <= 0:
                del self.spring_anim[k]
        if self.dead_t > 0:
            sim.t += 1
            self.dead_t -= 1
            if self.dead_t == 0:
                if self.mode == 'endless' and self.endless['lives'] <= 0:
                    self.end_endless()
                    return
                if not self.respawn_hook():
                    sim.reset_player(*sim.respawn)
                    sim.inv = 45
                    self.flash = 6
                    self.burst(sim.x + PS / 2, sim.y + PS / 2, C_CYAN, 10, 1.2, 18)
        else:
            if 'r' in self.events:
                self.on_death(manual=True)
            else:
                lat, jp, jh = self.read_input()
                ev = sim.step(lat, jp, jh, self.dash_key())
                self.handle_events(ev)
                if not sim.dead:
                    self.post_step(ev)
        self.update_fx()
        self.update_camera()

    def pre_step(self):
        return False

    def post_step(self, ev):
        pass

    def respawn_hook(self):
        return False

    def dash_key(self):
        return False

    def handle_events(self, ev):
        sim, lvl = self.sim, self.lvl
        cx, cy = sim.x + PS / 2.0, sim.y + PS / 2.0
        g = sim.eff
        gx, gy = GVEC[g]
        fx, fy = cx + gx * PS / 2, cy + gy * PS / 2
        for e in ev:
            if e == 'jump':
                self.sfx('jump')
                self.burst(fx, fy, '#6a6296', 4, 0.9, 14)
            elif e == 'land':
                self.sfx('land')
                self.burst(fx, fy, '#6a6296', 5, 1.0, 14)
            elif e == 'door':
                self.on_door()
                return
            elif e == 'death':
                self.on_death()
                return
            elif isinstance(e, tuple):
                k = e[0]
                if k == 'crystal':
                    self.sfx('crystal_' + DNAME[e[1]])
                    self.burst(cx, cy, DIRCOL[e[1]], 14, 1.8, 24)
                    self.flash = 2
                elif k == 'spring':
                    self.sfx('spring')
                    self.spring_anim[(e[1]['c'], e[1]['r'])] = 10
                    self.burst(cx, cy, '#ff6ad5', 8, 1.5, 18)
                elif k == 'field':
                    self.sfx('field')
                elif k == 'soul':
                    s = lvl.souls[e[1]]
                    self.stats['souls'] += 1
                    self.sfx('soul')
                    self.burst(s['x'] + 4, s['y'] + 4, C_CYAN, 12, 1.6, 22)
                elif k == 'cp':
                    cp = lvl.cps[e[1]]
                    self.sfx('check')
                    self.burst(cp['x'] + 8, cp['y'] + 8, C_GOLD, 16, 1.8, 28)
                    self.toast = ['CHECKPOINT', 100]
                elif k == 'crumble':
                    self.sfx('crumble')
                    self.burst(e[1][1] * TILE + 8, e[1][0] * TILE + 8, '#8a7a60', 8, 1.2, 20)
        if sim.on_ground and abs(sim.vx if g < 2 else sim.vy) > 1.5 and self.t % 7 == 0:
            self.burst(fx, fy, '#4a4380', 1, 0.5, 12)

    def on_death(self, manual=False):
        sim = self.sim
        sim.dead = True
        self.dead_t = 42
        self.stats['deaths'] += 1
        self.save['stats']['deaths'] += 1
        if self.save['opts']['shake']:
            self.shake = 14
        self.sfx('reset' if manual else 'death')
        x, y = sim.x + PS / 2.0, sim.y + PS / 2.0
        sk = SKINS[self.save['opts']['skin']][2]
        self.burst(x, y, sk['c'], 14, 2.4, 34, 1.5)
        self.burst(x, y, C_CYAN, 6, 2.0, 30)
        self.burst(x, y, C_RED, 6, 2.0, 30)
        if self.mode == 'endless':
            self.endless['lives'] -= 1

    def on_door(self):
        lvl, sim = self.lvl, self.sim
        secs = self.stats['frames'] / 60.0
        total = len(lvl.souls)
        got = self.stats['souls']
        stars = 1 + (1 if got >= total else 0) + (1 if secs <= lvl.par else 0)
        self.result = dict(secs=secs, got=got, total=total, stars=stars,
                           deaths=self.stats['deaths'], new=False, bonus=0)
        st = self.save['stats']
        st['souls'] += got
        st['frames'] += self.stats['frames']
        self.unlock_msg = None
        if self.mode == 'campaign':
            key = str(self.li)
            before = self.total_stars()
            best = self.save['best'].get(key)
            if not best or stars > best['stars'] or (stars == best['stars'] and secs < best['secs']):
                self.save['best'][key] = dict(secs=round(secs, 2), souls=got, stars=stars)
                self.result['new'] = True
            self.save['unlocked'] = max(self.save['unlocked'], min(len(LEVELS), self.li + 2))
            after = self.total_stars()
            for i, sk in enumerate(SKINS):
                if before < sk[1] <= after:
                    self.unlock_msg = 'NEW CLOAK: ' + sk[0]
        elif self.mode == 'endless':
            e = self.endless
            floors = len(lvl.spec['rooms']) - 2
            bonus = floors * 100 + got * 10 + max(0, int(lvl.par - secs)) * 2
            e['score'] += bonus
            e['floors'] += floors
            e['souls'] += got
            self.result['bonus'] = bonus
            while e['souls'] >= e['nextlife']:
                e['nextlife'] += 25
                if e['lives'] < 9:
                    e['lives'] += 1
                    self.unlock_msg = 'EXTRA LIFE!'
        else:
            b = self.save['daily'].get(self.daily_key)
            if not b or secs < b['secs']:
                self.save['daily'][self.daily_key] = dict(secs=round(secs, 2), souls=got)
                self.result['new'] = True
        self.write_save()
        self.sfx('clear')
        self.burst(lvl.door[0] + 8, lvl.door[1] + 16, THEMES[lvl.theme]['accent'], 30, 2.4, 40)
        self.goto(lambda: self.set_state('clear'))

    def end_endless(self):
        e = self.endless
        b = self.save['endless']
        e['new'] = e['score'] > b['score']
        if e['new']:
            b['score'] = e['score']
        b['sections'] = max(b['sections'], e['section'])
        self.write_save()
        self.sfx('gameover')
        self.goto(lambda: self.set_state('gameover'))

    def update_fx(self):
        for q in self.particles:
            q[0] += q[2]
            q[1] += q[3]
            q[3] += 0.03
            q[4] -= 1
        self.particles = [q for q in self.particles if q[4] > 0][:300]
        T = THEMES[self.lvl.theme]
        rise = T['amb'][0] == 'rise'
        for e in self.embers:
            e[1] += (-e[2] if rise else e[2] * 0.8)
            e[0] += math.sin(e[3] + self.t * 0.03) * (0.2 if rise else 0.35)

    def update_camera(self):
        s, lvl = self.sim, self.lvl
        tx = s.x + PS / 2.0 + max(-22, min(22, s.vx * 7))
        if lvl.ring:
            d = wrapd(tx - self.camx, lvl.wpx)
            self.camx = (self.camx + d * 0.16) % lvl.wpx
        else:
            lo, hi = self.VW / 2.0, lvl.wpx - self.VW / 2.0
            tx = lvl.wpx / 2.0 if hi < lo else max(lo, min(hi, tx))
            self.camx += (tx - self.camx) * 0.16
        ty = s.y + PS / 2.0 + max(-24, min(24, s.vy * 7))
        self.camy += (self.clamp_cam(ty) - self.camy) * 0.12

    # ======================================================================
    #  RENDER
    # ======================================================================
    def render(self):
        self.canvas.delete('all')
        st = self.state
        if st == 'title':
            self.draw_tower_scene(True)
            self.draw_title_menu()
        elif st in ('howto', 'select', 'options', 'ending', 'gameover'):
            self.draw_tower_scene(False)
            getattr(self, 'draw_' + st)()
        elif st == 'intro':
            self.draw_intro()
        elif st in ('play', 'pause'):
            self.draw_world()
            self.draw_hud()
            if st == 'pause':
                self.draw_pause()
        elif st == 'clear':
            self.draw_world()
            self.draw_clear()
        if self.trans:
            self.draw_shutters()

    def draw_shutters(self):
        tr = self.trans
        f = tr['t'] / 14.0
        amt = f if tr['ph'] == 0 else 1.0 - f
        amt = max(0.0, min(1.0, amt))
        if amt <= 0:
            return
        h = amt * self.VH / 2.0 + 0.5
        self.rect(0, 0, self.VW, h, C_SHUTTER)
        self.rect(0, self.VH - h, self.VW, h, C_SHUTTER)
        self.rect(0, h, self.VW, 1, C_EDGE)
        self.rect(0, self.VH - h - 1, self.VW, 1, C_EDGE)

    # -- title scene --------------------------------------------------------
    def draw_tower_scene(self, with_title):
        VW, VH, t = self.VW, self.VH, self.t
        cx = VW / 2.0
        self.rect(0, 0, VW, VH, '#07060f')
        self.rect(0, VH * 0.45, VW, VH * 0.55, '#0a0818')
        for (sx, sy, ph) in self.stars:
            tw = math.sin(t * 0.04 + ph)
            col = '#c9c3f2' if tw > 0.4 else ('#6a64a0' if tw > -0.4 else '#2a2650')
            self.rect(sx * VW, sy * VH, 1, 1, col)
        mx, my, mr = VW * 0.8, 38, 15
        for dy in range(-mr, mr + 1):
            hw = math.sqrt(max(0, mr * mr - dy * dy))
            self.rect(mx - hw, my + dy, hw * 2, 1, '#cfd0ee' if dy < 4 else '#b4b6dc')
        self.rect(mx - 6, my - 5, 4, 3, '#a2a4cc')
        self.rect(mx + 3, my + 3, 5, 4, '#a2a4cc')
        self.rect(mx - 3, my + 8, 3, 3, '#a2a4cc')
        self.tower_rings(cx, True)
        ground = VH - 14
        self.rect(cx - 40, ground - 20, 80, 40, '#120e24')
        self.rect(cx - 26, 62, 52, ground - 62, '#15112b')
        self.rect(cx + 10, 62, 16, ground - 62, '#0f0b20')
        self.rect(cx - 26, 62, 2, ground - 62, '#201a3d')
        for y in range(70, int(ground), 8):
            self.rect(cx - 26, y, 52, 1, '#100c22')
        self.rect(cx - 32, 46, 64, 18, '#17132e')
        self.rect(cx + 14, 46, 18, 18, '#110d24')
        for i in range(8):
            self.rect(cx - 32 + i * 8, 40, 5, 6, '#17132e')
        for i in range(22):
            w = 6 + i * 2.4
            self.rect(cx - w / 2.0, 18 + i, w, 1, '#1a1534' if i % 2 else '#1d1838')
        self.rect(cx - 0.5, 8, 1, 10, '#2a2450')
        self.rect(cx - 1.5, 5, 3, 3, C_RED if (t // 20) % 2 == 0 else '#7a1230')
        for i, (wx, wy) in enumerate(((-14, 72), (6, 72), (-14, 98), (6, 98),
                                      (-14, 124), (6, 124), (-4, 52))):
            if wy > ground - 6:
                continue
            on = math.sin(t * 0.05 + i * 1.9) > -0.35
            self.rect(cx + wx, wy, 5, 9, '#ffb04a' if on else '#3a2630')
            if on:
                self.rect(cx + wx + 1, wy + 1, 2, 3, '#ffe9a0')
        self.rect(cx - 30, 86, 60, 2, '#1d1840')
        self.rect(cx - 30, 112, 60, 2, '#1d1840')
        self.rect(0, ground, VW, VH - ground, '#0c0a1a')
        self.tower_rings(cx, False)
        if with_title:
            self.wave_text('THE', cx, 6, 2, C_GOLD, 1.2, 0.07)
            self.wave_text('TURNING TOWER', cx, 18, 3, C_GOLD, 2.0, 0.07)
            self.wave_text('UP AND DOWN, ROUND AND ROUND', cx, 38, 1, C_PURPLE, 1.5, 0.09,
                           shadow='#000000')

    def tower_rings(self, cx, back):
        t = self.t
        cols = ('#8ff7ff', '#a56bff', '#f0c75e')
        for k in range(3):
            ycen = 70 + k * 30 + math.sin(t * 0.02 + k * 2.0) * 5
            rx, ry = 56 + k * 12, 9 + k * 2
            spd = (0.018 + k * 0.006) * (1 if k % 2 == 0 else -1)
            n = 16
            for i in range(n):
                a = t * spd + i * 2 * math.pi / n
                s = math.sin(a)
                if (s < 0) != back:
                    continue
                sz = 2 if s > 0.2 else 1
                self.rect(cx + math.cos(a) * rx - sz / 2.0, ycen + s * ry - sz / 2.0, sz, sz,
                          cols[k] if s > 0 else '#3a3470')

    def draw_title_menu(self):
        items = self.title_items()
        x = 22
        y = self.VH * 0.47
        for i, it in enumerate(items):
            sel = i == self.menu
            if sel:
                self.text('>', x - 7 + (1 if (self.t // 15) % 2 else 0), y, C_GOLD)
            self.text(it, x, y, C_TEXT if sel else C_DIM, 1)
            y += 10
        e = self.save['endless']
        if e['score']:
            self.text('ENDLESS BEST %d' % e['score'], self.VW - 8, 6, C_FAINT, 1, 'r')
        self.text('STARS %d' % self.total_stars(), self.VW - 8, 13, C_GOLD, 1, 'r')
        self.text('UP DOWN: CHOOSE   ENTER: OK', 8, self.VH - 10, C_FAINT, 1)
        self.text('GMI GAME JAM 2026', self.VW - 8, self.VH - 10, C_FAINT, 1, 'r')

    def draw_howto(self):
        VW = self.VW
        w, h = 250, 150
        x, y = (VW - w) / 2.0, 14
        self.panel(x, y, w, h)
        self.text('HOW TO PLAY', VW / 2.0, y + 6, C_GOLD, 2, 'c')
        lines = [('A D / ARROWS', 'MOVE ALONG YOUR SURFACE'),
                 ('SPACE / Z / K', 'JUMP'),
                 ('KEY AWAY FROM FLOOR', 'ALSO JUMPS'),
                 ('R', 'RESPAWN'), ('ESC / P', 'PAUSE   M MUTE')]
        yy = y + 24
        for a, b in lines:
            self.text(a, x + 8, yy, C_CYAN)
            self.text(b, x + 104, yy, C_TEXT)
            yy += 9
        yy += 4
        for col, s in ((C_DIM, 'GRAVITY IS IN THE TOWER, NOT ON A KEY:'),
                       (DIRCOL[UP], 'CRYSTALS SET GRAVITY UP DOWN LEFT RIGHT'),
                       (DIRCOL[RIGHT], 'WIND FIELDS PUSH YOU WHILE INSIDE'),
                       (C_DIM, 'WALK ON WALLS: PRESS UP DOWN TO CLIMB'),
                       (C_DIM, 'THE TOWER IS A RING. GO ROUND AND ROUND.'),
                       (C_DIM, 'SPRINGS LAUNCH. CRACKED STONE CRUMBLES.'),
                       (C_DIM, 'SPIKES SAWS WISPS KILL. SOULS ARE STARS.'),
                       (C_DIM, 'WALK INTO AN UPDRAFT TO RISE A FLOOR.')):
            self.text(s, x + 8, yy, col)
            yy += 8
        self.text('PRESS ENTER', VW / 2.0, y + h - 9, C_FAINT, 1, 'c')

    def draw_options(self):
        VW = self.VW
        o = self.save['opts']
        w, h = 190, 126
        x, y = (VW - w) / 2.0, 22
        self.panel(x, y, w, h)
        self.text('OPTIONS', VW / 2.0, y + 6, C_GOLD, 2, 'c')
        sk = SKINS[o['skin']]
        rows = ['MUSIC     < %d >' % o['music'], 'SOUND FX  < %d >' % o['sfx'],
                'SHAKE     < %s >' % ('ON' if o['shake'] else 'OFF'),
                'CLOAK     < %s >' % sk[0], 'BACK']
        yy = y + 26
        for i, r in enumerate(rows):
            sel = i == self.menu
            if sel:
                self.text('>', x + 8, yy, C_GOLD)
            self.text(r, x + 18, yy, C_TEXT if sel else C_DIM)
            yy += 11
        self.img(self.assets.player('stand', 1, DOWN, o['skin']), x + w - 28, y + 58)
        nxt = [s for s in SKINS if s[1] > self.total_stars()]
        if nxt:
            self.text('NEXT CLOAK AT %d STARS' % nxt[0][1], VW / 2.0, y + 83, C_FAINT, 1, 'c')
        st = self.save['stats']
        self.text('DEATHS %d   SOULS %d' % (st['deaths'], st['souls']), VW / 2.0, y + 94, C_DIM, 1, 'c')
        self.text('TIME %s   STARS %d' % (fmt_time(st['frames'] / 60.0), self.total_stars()),
                  VW / 2.0, y + 103, C_DIM, 1, 'c')
        self.text('LEFT RIGHT: CHANGE', VW / 2.0, y + h - 9, C_FAINT, 1, 'c')

    def draw_select(self):
        VW = self.VW
        n = len(LEVELS)
        vis = 9
        off = max(0, min(n - vis, self.sel - 4))
        w, h = 270, 136
        x, y = (VW - w) / 2.0, 14
        self.panel(x, y, w, h)
        self.text('LEVEL SELECT', VW / 2.0, y + 5, C_GOLD, 2, 'c')
        yy = y + 20
        for i in range(off, off + vis):
            spec = LEVELS[i]
            sel = i == self.sel
            locked = i >= self.save['unlocked']
            col = C_FAINT if locked else (C_TEXT if sel else C_DIM)
            if sel:
                self.rect(x + 3, yy - 2, w - 6, 11, '#1d1840')
                self.text('>', x + 6, yy, C_GOLD)
            self.rect(x + 14, yy, 3, 7, THEMES[spec['theme']]['accent'] if not locked else '#2a2450')
            self.text('%d' % (i + 1), x + 20, yy, col)
            self.text(spec['name'] if not locked else '???', x + 32, yy, col)
            self.img(self.assets.arrow5(DOWN if spec['inv'] else UP, C_CYAN if not locked else '#2a2450'),
                     x + 170, yy + 1)
            best = self.save['best'].get(str(i))
            if best:
                for s in range(3):
                    self.img(self.assets.star(s < best['stars']), x + 182 + s * 8, yy)
                self.text(fmt_time(best['secs']), x + w - 6, yy, C_DIM, 1, 'r')
            elif locked:
                self.text('LOCKED', x + w - 6, yy, C_FAINT, 1, 'r')
            yy += 12
        self.text('ENTER: PLAY   ESC: BACK', VW / 2.0, y + h + 4, C_FAINT, 1, 'c')

    def draw_ending(self):
        VW = self.VW
        cx = VW / 2.0
        self.wave_text('YOU CONQUERED THE TOWER', cx, 12, 2, C_GOLD, 1.5, 0.08)
        self.text('AND THE TOWER TURNS ON.', cx, 34, C_PURPLE, 1, 'c')
        st = self.save['stats']
        w, h = 170, 62
        x, y = cx - w / 2.0, 96
        self.panel(x, y, w, h)
        self.text('STARS  %d / %d' % (self.total_stars(), len(LEVELS) * 3), x + 12, y + 8, C_GOLD)
        self.text('DEATHS %d' % st['deaths'], x + 12, y + 18, C_RED)
        self.text('SOULS  %d' % st['souls'], x + 12, y + 28, C_CYAN)
        self.text('TRY THE ENDLESS TOWER', cx, y + 42, C_GOLD, 1, 'c')
        self.text('PRESS ENTER', cx, self.VH - 10, C_FAINT, 1, 'c')

    def draw_gameover(self):
        VW = self.VW
        cx = VW / 2.0
        e = self.endless
        self.wave_text('THE TOWER KEEPS YOU', cx, 14, 2, C_RED, 1.5, 0.08)
        w, h = 160, 70
        x, y = cx - w / 2.0, 70
        self.panel(x, y, w, h)
        self.text('SCORE    %d' % e['score'], x + 12, y + 8, C_GOLD)
        self.text('SECTION  %d' % e['section'], x + 12, y + 18, C_PURPLE)
        self.text('FLOORS   %d' % e['floors'], x + 12, y + 28, C_TEXT)
        self.text('SOULS    %d' % e['souls'], x + 12, y + 38, C_CYAN)
        if e.get('new'):
            self.text('NEW HIGH SCORE!', cx, y + 52, C_GOLD, 1, 'c')
        else:
            self.text('BEST %d' % self.save['endless']['score'], cx, y + 52, C_DIM, 1, 'c')
        self.text('PRESS ENTER', cx, self.VH - 10, C_FAINT, 1, 'c')

    # -- intro card ---------------------------------------------------------
    def draw_intro(self):
        VW, VH, t = self.VW, self.VH, self.t
        lvl = self.lvl
        T = THEMES[lvl.theme]
        self.rect(0, 0, VW, VH, '#06050c')
        mx, my = VW / 2.0, VH / 2.0
        for k, (rad, n, spd) in enumerate(RINGS):
            for i in range(n):
                a = t * 0.01 * spd + i * 2 * math.pi / n
                self.rect(mx + math.cos(a) * rad * 1.3, my + math.sin(a) * rad * 0.7, 1, 1,
                          T['ring'][1] if i % 5 == 0 else T['ring'][0])
        if self.mode == 'endless':
            head = 'SECTION %d' % self.endless['section']
        elif self.mode == 'daily':
            head = 'DAILY TOWER'
        else:
            head = 'FLOOR %d' % (self.li + 1)
        self.text(T['name'], mx, my - 46, T['accent'], 1, 'c')
        self.text(head, mx, my - 36, C_PURPLE, 2, 'c')
        self.wave_text(lvl.name if self.mode == 'campaign' else '', mx, my - 18, 2, C_GOLD, 1.2, 0.08)
        self.text(lvl.sub, mx, my + 2, C_TEXT, 1, 'c')
        down = lvl.inverted
        bob = math.sin(t * 0.1) * 3
        self.img(self.assets.arrow5(DOWN if down else UP, C_CYAN), mx - 2.5, my + 18 + (-bob if down else bob))
        self.text('%s  %d FLOORS' % ('DESCEND' if down else 'CLIMB', len(lvl.spec['rooms']) - 2),
                  mx, my + 32, C_CYAN, 1, 'c')
        if self.mode == 'endless':
            self.text('LIVES %d   SCORE %d' % (self.endless['lives'], self.endless['score']),
                      mx, my + 44, C_GOLD, 1, 'c')
        if self.intro_t > 20 and (t // 25) % 2 == 0:
            self.text('PRESS ENTER', mx, VH - 14, C_FAINT, 1, 'c')

    # -- world --------------------------------------------------------------
    def draw_scene(self, lvl, sim, cx, cy, edit=False):
        A = self.assets
        VW, VH, t = self.VW, self.VH, self.t
        th = lvl.theme
        T = THEMES[th]
        if sim is None:
            sim = _EditSim(lvl, t)

        def sx(wx):
            return lvl.wd(wx - cx) + VW / 2.0

        def sy(wy):
            return wy - cy + VH / 2.0

        bg = A.bg(th)
        ox = -((cx * 0.45) % 64)
        oy = -((cy * 0.45) % 64)
        y = oy
        while y < VH:
            x = ox
            while x < VW:
                self.img(bg, x, y)
                x += 64
            y += 64
        mx, my = VW / 2.0, VH / 2.0
        for k, (rad, n, spd) in enumerate(RINGS):
            a0 = (cx * 0.003 + cy * 0.004) * spd * 3 + t * 0.003 * spd
            for i in range(n):
                a = a0 + i * 2 * math.pi / n
                big = i % 6 == 0
                self.rect(mx + math.cos(a) * rad * 1.5, my + math.sin(a) * rad * 0.9,
                          2 if big else 1, 2 if big else 1, T['ring'][1] if big else T['ring'][0])
        for (wx, wy) in lvl.windows:
            x = sx(wx)
            if -30 < x < VW + 6:
                yy = sy(wy)
                if -50 < yy < VH:
                    self.img(A.window(th), x, yy)
        for (wx, wy, ln) in lvl.chains:
            x = sx(wx)
            if -10 < x < VW + 4:
                for i in range(ln):
                    yy = sy(wy + i * TILE)
                    if -16 < yy < VH:
                        self.img(A.chain(), x, yy)
        for (wx, wy) in lvl.torches:
            x = sx(wx)
            if -40 < x < VW + 40:
                yy = sy(wy)
                if -40 < yy < VH + 40:
                    self.img(A.glow(th), x + 4 - 22, yy + 4 - 22)
        for (wx, wy) in lvl.torches:
            x = sx(wx)
            if -10 < x < VW + 4:
                yy = sy(wy)
                if -16 < yy < VH:
                    self.img(A.torch(th, (t // 7 + int(wx)) % 2), x, yy)

        movers = lvl.movers(sim.t)
        for o in lvl.orbits:
            x0 = sx(o['cx'])
            if -80 < x0 < VW + 80:
                for i in range(20):
                    a = i * math.pi * 2 / 20
                    self.rect(x0 + o['rx'] * math.cos(a), sy(o['cy'] + o['ry'] * math.sin(a)),
                              1, 1, '#3a1226')
        for s in lvl.saws:
            x0 = sx(s['cx'])
            if -80 < x0 < VW + 80:
                for i in range(-s['half'], s['half'] + 1, 4):
                    self.rect(x0 + i, sy(s['cy']), 1, 1, '#3a2a3a')

        c0 = int(math.floor((cx - VW / 2.0) / TILE))
        c1 = int(math.floor((cx + VW / 2.0) / TILE)) + 1
        r0 = max(0, int(math.floor((cy - VH / 2.0) / TILE)))
        r1 = min(lvl.R - 1, int(math.floor((cy + VH / 2.0) / TILE)))
        fr = (t // 18) % 2
        ff = (t // 4) % 4
        for r in range(r0, r1 + 1):
            row = lvl.g[r]
            drow = lvl.deco[r]
            y = r * TILE - cy + VH / 2.0
            for ci in range(c0, c1 + 1):
                if not lvl.ring and (ci < 0 or ci >= lvl.W):
                    continue
                c = ci % lvl.W
                v = row[c]
                x = ci * TILE - cx + VW / 2.0
                if v == 0:
                    fm = lvl.fieldmap.get((r, c))
                    if fm:
                        self.img(A.field(th, fm[0], ff), x, y)
                    continue
                if v == 1:
                    var, top, bot, rune = drow[c]
                    self.img(A.brick(th, var, top, bot, rune, fr), x, y)
                elif v == 6:
                    k = (r, c)
                    if k in sim.gone:
                        continue
                    if k in sim.crumb:
                        x += random.choice((-1, 0, 1))
                    self.img(A.crumble(th, 1 if k in sim.crumb else 0), x, y)
                else:
                    self.img(A.spike(SPIKE_DIR[v]), x, y)

        dx = sx(lvl.door[0]) if lvl.door else -99
        if -20 < dx < VW + 20:
            self.img(A.door(th, (t // 10) % 2, lvl.inverted), dx, sy(lvl.door[1]))
        for cr in lvl.crystals:
            x = sx(cr['x'])
            if -20 < x < VW + 20:
                yy = sy(cr['y']) + math.sin(t * 0.08 + cr['c']) * 1.2
                self.img(A.crystal(cr['d'], (t // 10) % 2), x, yy)
        for sp in lvl.springs:
            x = sx(sp['x'])
            if -20 < x < VW + 20:
                self.img(A.spring(sp['d'], 1 if (sp['c'], sp['r']) in self.spring_anim else 0),
                         x, sy(sp['y']))
        for i, cp in enumerate(lvl.cps):
            x = sx(cp['x'])
            if -20 < x < VW + 20:
                self.img(A.brazier(th, sim.lit[i], t // 6, lvl.inverted), x, sy(cp['y']))
        for i, s in enumerate(lvl.souls):
            if sim.souls[i]:
                continue
            x = sx(s['x'])
            if -10 < x < VW + 10:
                self.img(A.page() if s.get('page') is not None else A.orb((t // 12) % 2), x, sy(s['y']) + math.sin(t * 0.06 + s['c']) * 1.5)
        no = len(lvl.orbits)
        for i, (wx, wy, rad) in enumerate(movers):
            x = sx(wx)
            if -12 < x < VW + 12:
                if i < no:
                    self.img(A.wisp((t // 5) % 2), x - 4, sy(wy) - 4)
                else:
                    self.img(A.saw((t // 2) % 4), x - 6, sy(wy) - 6)

        self.draw_ents(lvl, sim, sx, sy)

    def draw_ents(self, lvl, sim, sx, sy):
        pass

    def draw_world(self):
        lvl, sim, A = self.lvl, self.sim, self.assets
        VW, VH, t = self.VW, self.VH, self.t
        th = lvl.theme
        T = THEMES[th]
        shx = shy = 0
        if self.shake > 0:
            shx, shy = random.randint(-1, 1), random.randint(-1, 1)
        cx, cy = self.camx + shx, self.camy + shy
        self.draw_scene(lvl, sim, cx, cy)

        def sx(wx):
            return lvl.wd(wx - cx) + VW / 2.0

        def sy(wy):
            return wy - cy + VH / 2.0

        if self.dead_t == 0:
            blink = sim.inv > 0 and (t // 3) % 2 == 0 and sim.inv < 38
            if not blink:
                g = sim.eff
                lat_v = sim.vx if g < 2 else sim.vy
                if not sim.on_ground:
                    fn = 'air'
                elif abs(lat_v) > 0.3:
                    fn = 'runA' if int(sim.anim) % 2 == 0 else 'runB'
                else:
                    fn = 'stand'
                face = sim.face if g != RIGHT else -sim.face
                im = A.player(fn, 1 if face > 0 else -1, g, self.save['opts']['skin'])
                if g == DOWN:
                    px, py = sim.x - 2.5, sim.y + PS - 16
                elif g == UP:
                    px, py = sim.x - 2.5, sim.y
                elif g == LEFT:
                    px, py = sim.x, sim.y - 2.5
                else:
                    px, py = sim.x + PS - 16, sim.y - 2.5
                self.img(im, sx(px), sy(py))

        for q in self.particles:
            s = q[6]
            self.rect(sx(q[0]) - s / 2.0, sy(q[1]) - s / 2.0, s, s, q[5])
        kind, cols = T['amb']
        for e in self.embers:
            self.rect(e[0] % VW, e[1] % VH, 1, 1, cols[e[4]])

        if self.state in ('play', 'pause'):
            pcx, pcy = sim.x + PS / 2.0, sim.y + PS / 2.0
            for h in lvl.hints:
                dxh = lvl.wd(h['x'] - pcx)
                dyh = h['y'] - pcy
                if abs(dxh) < 130 and abs(dyh) < 80:
                    self.text(h['text'], sx(h['x']), sy(h['y']),
                              C_TEXT if abs(dxh) < 70 else C_FAINT, 1, 'c')
        if self.flash > 0:
            self.rect(0, 0, VW, VH, '#d8d0ff' if self.flash > 3 else '#6a6296')

    # -- HUD ----------------------------------------------------------------
    def draw_hud(self):
        lvl, sim, A = self.lvl, self.sim, self.assets
        VW, VH = self.VW, self.VH
        T = THEMES[lvl.theme]
        if self.mode == 'campaign':
            self.text('FLOOR %d' % (self.li + 1), 6, 5, T['accent'], 1)
        elif self.mode == 'endless':
            self.text('SECTION %d' % self.endless['section'], 6, 5, T['accent'], 1)
        else:
            self.text({'custom': 'CUSTOM LEVEL', 'test': 'TEST PLAY'}.get(self.mode, 'DAILY TOWER'), 6, 5, T['accent'], 1)
        self.text(lvl.name, 6, 12, C_DIM, 1)
        self.img(A.orb(0), 6, 20)
        self.text('%d/%d' % (self.stats['souls'], len(lvl.souls)), 16, 21, C_CYAN, 1)
        self.text(fmt_time(self.stats['frames'] / 60.0), VW / 2.0, 5, C_TEXT, 1, 'c')
        if self.mode == 'endless':
            e = self.endless
            for i in range(min(9, e['lives'])):
                self.img(A.heart(True), VW - 70 + i * 8, 5)
            self.text('%d' % e['score'], VW - 28, 14, C_GOLD, 1, 'r')
        else:
            self.text('DEATHS %d' % self.stats['deaths'], VW - 28, 5, C_RED, 1, 'r')
        x0, y0 = VW - 24, 4
        self.panel(x0, y0, 17, 17)
        eff = sim.eff
        for d, (ax, ay) in ((UP, (6, 1)), (DOWN, (6, 11)), (LEFT, (1, 6)), (RIGHT, (11, 6))):
            self.img(A.arrow5(d, DIRCOL[d] if d == eff else '#2a2450'), x0 + ax, y0 + ay)
        mxb = VW - 9
        top, bot = 30, VH - 14
        self.rect(mxb, top, 2, bot - top, '#2a2450')
        for (a, b) in lvl.bounds:
            self.rect(mxb - 2, top + (bot - top) * a / float(lvl.R), 6, 1, '#4d4399')
        if lvl.door:
            df = (lvl.door[1] + 16) / float(lvl.hpx)
            self.rect(mxb - 2, top + (bot - top) * df - 2, 6, 4, C_GOLD)
        pf = (sim.y + PS / 2.0) / float(lvl.hpx)
        self.rect(mxb - 1, top + (bot - top) * pf - 2, 4, 4, C_CYAN)
        if self.toast:
            self.text(self.toast[0], VW / 2.0, 22, C_GOLD, 1, 'c')

    def draw_pause(self):
        VW, VH = self.VW, self.VH
        w, h = 120, 70
        x, y = (VW - w) / 2.0, (VH - h) / 2.0
        self.panel(x, y, w, h)
        self.text('PAUSED', VW / 2.0, y + 6, C_GOLD, 2, 'c')
        yy = y + 24
        for i, it in enumerate(self.pause_items()):
            sel = i == self.menu
            if sel:
                self.text('>', x + 10, yy, C_GOLD)
            self.text(it, x + 20, yy, C_TEXT if sel else C_DIM)
            yy += 10

    def draw_clear(self):
        VW, VH = self.VW, self.VH
        r = self.result
        w, h = 180, 108
        x, y = (VW - w) / 2.0, (VH - h) / 2.0
        self.panel(x, y, w, h)
        head = {'campaign': 'FLOOR %d CLEAR' % (self.li + 1), 'endless': 'SECTION CLEAR',
                'daily': 'DAILY CLEAR'}.get(self.mode, 'LEVEL CLEAR')
        self.text(head, VW / 2.0, y + 6, C_GOLD, 2, 'c')
        self.text(self.lvl.name, VW / 2.0, y + 23, THEMES[self.lvl.theme]['accent'], 1, 'c')
        for s in range(3):
            self.img(self.assets.star(s < r['stars']), VW / 2.0 - 14 + s * 10, y + 32)
        secs = r['secs']
        self.text('TIME    %s   PAR %s' % (fmt_time(secs), fmt_time(self.lvl.par)), x + 12, y + 45, C_TEXT)
        self.text('SOULS   %d/%d' % (r['got'], r['total']), x + 12, y + 54, C_CYAN)
        self.text('DEATHS  %d' % r['deaths'], x + 12, y + 63, C_RED)
        if self.mode == 'endless':
            self.text('SCORE   +%d = %d' % (r['bonus'], self.endless['score']), x + 12, y + 72, C_GOLD)
        elif r['new']:
            self.text('NEW BEST!', x + 12, y + 72, C_GOLD)
        if self.unlock_msg:
            self.text(self.unlock_msg, VW / 2.0, y + 82, C_PURPLE, 1, 'c')
        elif self.mode == 'campaign':
            self.text('3 STARS: ALL SOULS AND UNDER PAR', VW / 2.0, y + 82, C_FAINT, 1, 'c')
        if (self.t // 25) % 2 == 0:
            self.text('PRESS ENTER', VW / 2.0, y + h - 9, C_DIM, 1, 'c')


# ============================================================================
#  GAME v3  (menus, editor / music maker / story integration)
# ============================================================================
TITLE_ITEMS = ['STORY MODE', 'CAMPAIGN', 'LEVEL SELECT', 'ENDLESS TOWER', 'DAILY TOWER', 'LEVEL EDITOR',
               'MY LEVELS', 'LEVEL PORTAL', 'MUSIC MAKER', 'OPTIONS', 'HOW TO PLAY', 'QUIT']
NPC_NAMES = dict(mira='MIRA', brin='BRIN', tock='TOCK', cog='COG', bellows='BELLOWS', ghost='GHOST')
MOUSE_STATES = ('editor', 'music', 'custom')


class GameV3(StoryMixin, Game):
    def post_init(self):
        self.mev = []
        self.mx = self.my = 0.0
        self.mdown = set()
        self.chars = []
        self.editor = None
        self.mm = None
        self.test_editor = None
        self.custom_files = []
        self.custom_i = 0
        self.custom_meta = {}
        self.theme_song = None
        self.cursor = 'none'
        
        # --- SHUTDOWN & PORTAL STATE FLAGS ---
        self.running = True
        self.portal_tab = 0        # 0: Levels, 1: Music
        self.portal_i = 0
        self.portal_items = []
        self.portal_msg = ""
        self.portal_search = ""
        self.portal_loading = False
        self.portal_edit = None    # open search box (dict) or None
        self.portal_req = 0        # id of the newest fetch; older replies are dropped
        self.portal_inbox = []     # worker thread -> main thread (fetch results)
        self.portal_dl_busy = False
        self.portal_busy = False     # login / publish in flight
        self.portal_mode = 'browse'  # 'browse' or 'publish' (pick a local file)
        self.portal_pub_files, self.portal_pub_i = [], 0
        self.portal_pub_pick, self.portal_pub_kind, self.portal_login_user = '', 'level', ''
        self.import_q = []         # worker thread -> main thread (imports / downloads)
        # --------------------------------------
        
        self.start_download_watcher()
        self.story_init()
        s = self.save
        s.setdefault('story', {})
        s['opts'].setdefault('theme_song', None)
        self.apply_theme_song(restart=False)
        
        c = self.canvas
        mp = {1: 1, 2: 3, 3: 2} if sys.platform == 'darwin' else {1: 1, 2: 2, 3: 3}
        for b in (1, 2, 3):
            c.bind('<Button-%d>' % b, lambda e, b=b: self.m_down(mp[b], e))
            c.bind('<ButtonRelease-%d>' % b, lambda e, b=b: self.m_up(mp[b], e))
        c.bind('<Motion>', self.m_move)
        for b in (1, 2, 3):
            c.bind('<B%d-Motion>' % b, self.m_move)
        c.bind('<MouseWheel>', lambda e: self.mev.append(('wheel', -1 if e.delta > 0 else 1, 0, 0)))
        c.bind('<Button-4>', lambda e: self.mev.append(('wheel', -1, 0, 0)))
        c.bind('<Button-5>', lambda e: self.mev.append(('wheel', 1, 0, 0)))

    def m_move(self, e):
        self.mx, self.my = e.x / float(self.S), e.y / float(self.S)

    def m_down(self, b, e):
        self.m_move(e)
        self.mdown.add(b)
        self.mev.append(('down', b, self.mx, self.my))

    def m_up(self, b, e):
        self.m_move(e)
        self.mdown.discard(b)
        self.mev.append(('up', b, self.mx, self.my))

    def quit(self):
        self.running = False
        super().quit()

    # ======================================================================
    #  LEVEL PORTAL  (in-game browser for the community level / music server)
    # ======================================================================
    PORTAL_WEB = 'https://ttt-level-portal.on.websim.com'
    PORTAL_API = 'https://ttt-level-portal.on.websim.com/api/portal'
    PORTAL_TABS = ('NEWEST LEVELS', 'POPULAR LEVELS', 'CUSTOM MUSIC')
    PORTAL_UA = {'User-Agent': 'TheTurningTowerClient/1.0', 'Accept': 'application/json, text/plain, */*'}

    @staticmethod
    def _pstr(v, default='', n=None):
        """Safe, font-friendly (ASCII, upper-case) text from any JSON value."""
        s = default if v is None else str(v)
        s = ''.join(ch if ' ' <= ch <= '~' else ' ' for ch in s).strip().upper()
        return s[:n] if n else s

    @staticmethod
    def _portal_items(payload, tab):
        if isinstance(payload, dict):
            keys = (('music', 'tracks', 'songs', 'items', 'results', 'data', 'levels') if tab == 2
                    else ('levels', 'items', 'results', 'data'))
            found = []
            for k in keys:
                if isinstance(payload.get(k), list):
                    found = payload[k]
                    break
            payload = found
        if not isinstance(payload, list):
            return []
        return [i for i in payload if isinstance(i, dict)]

    def open_level_portal(self):
        """Opens the in-game portal browser and starts loading the first page."""
        self.state = 'online_browser'
        self.portal_tab = 0
        self.portal_i = 0
        self.portal_search = ''
        self.portal_edit = None
        self.portal_mode = 'browse'
        self.chars = []
        self.fetch_portal_page()

    def fetch_portal_page(self):
        """Loads the current tab on a worker thread; the result is picked up by upd_online_browser."""
        import urllib.request
        import urllib.parse
        import urllib.error
        self.portal_req += 1
        req_id, tab = self.portal_req, self.portal_tab
        self.portal_loading = True
        self.portal_items = []
        self.portal_i = 0
        self.portal_msg = 'FETCHING TRANSMISSIONS'
        qs = urllib.parse.quote(self.portal_search)
        api = self.PORTAL_API
        if tab == 0:
            url = f'{api}/levels?limit=100&offset=0&sort=newest&q={qs}'
        elif tab == 1:
            url = f'{api}/levels?limit=100&offset=0&sort=downloads&q={qs}'
        else:
            url = f'{api}/music?limit=100&offset=0&q={qs}'
        inbox, headers = self.portal_inbox, self.PORTAL_UA

        def worker():
            items, err = [], None
            try:
                rq = urllib.request.Request(url, headers=headers)
                with urllib.request.urlopen(rq, timeout=10) as resp:
                    raw = resp.read().decode('utf-8', 'replace')
                items = self._portal_items(json.loads(raw), tab)
            except urllib.error.HTTPError as ex:
                err = 'SERVER ERROR %d' % ex.code
            except (urllib.error.URLError, OSError):
                err = 'CANNOT REACH THE PORTAL SERVER'
            except ValueError:
                err = 'PORTAL REPLY COULD NOT BE READ'
            except Exception:
                err = 'PORTAL ERROR'
            inbox.append((req_id, items, err))

        threading.Thread(target=worker, daemon=True).start()

    def portal_poll(self):
        while self.portal_inbox:
            req_id, items, err = self.portal_inbox.pop(0)
            if req_id != self.portal_req:
                continue                      # reply for a tab / search we already left
            self.portal_loading = False
            self.portal_items = items
            self.portal_i = 0
            if err:
                self.portal_msg = err + '\nR: RETRY    O: OPEN THE WEB PORTAL'
            elif not items:
                self.portal_msg = 'NO RECORDS FOUND IN ARCHIVE'
            else:
                self.portal_msg = ''

    def download_portal_asset(self, item_id, asset_type='level'):
        """Downloads one level / song, validates it and files it in levels/ or music/."""
        import urllib.request
        import urllib.parse
        if self.portal_dl_busy:
            return
        self.portal_dl_busy = True
        music = asset_type == 'music'
        self.toast = ['DOWNLOADING ' + asset_type.upper(), 600]
        api, iid = self.PORTAL_API, urllib.parse.quote(str(item_id), safe='')
        metas = [f'{api}/music/{iid}/download'] if music else [f'{api}/levels/{iid}/download']
        head, headers, q = ('TTTM' if music else 'TTTL'), self.PORTAL_UA, self.import_q

        def fetch(u):
            with urllib.request.urlopen(urllib.request.Request(u, headers=headers), timeout=12) as r:
                return r.read().decode('utf-8-sig', 'replace')

        def worker():
            for meta in metas:
                try:
                    body, text = fetch(meta), None
                    if body.lstrip().startswith(head):
                        text = body
                    else:
                        dl = json.loads(body)
                        obj = dl.get('download') if isinstance(dl.get('download'), dict) else {}
                        for k in ('content', 'data', 'file', 'text'):
                            v = obj.get(k) or dl.get(k)
                            if isinstance(v, str) and v.lstrip().startswith(head):
                                text = v
                                break
                        if text is None:
                            u = obj.get('url') or obj.get('download_url') or dl.get('url') or dl.get('download_url')
                            if isinstance(u, str):
                                u = urllib.parse.urljoin(meta, u)   # handles relative URLs too
                            if isinstance(u, str) and u.startswith(('http://', 'https://')):
                                b2 = fetch(u)
                                if b2.lstrip().startswith(head):
                                    text = b2
                    if text is None:
                        continue
                    if music:
                        parsed = text_to_song(text)
                        folder, ext, out = MUSIC_DIR, '.tttm', song_to_text(parsed)
                    else:
                        parsed = text_to_data(text)
                        folder, ext, out = LEVELS_DIR, '.tttl', data_to_text(parsed)
                    os.makedirs(folder, exist_ok=True)
                    with open(os.path.join(folder, safe_name(parsed['name']) + ext), 'w', encoding='utf-8') as fo:
                        fo.write(out)
                    q.append(('ok', parsed['name'], music))
                    return
                except Exception:
                    continue
            q.append(('fail', 'DOWNLOAD FAILED', music))

        threading.Thread(target=worker, daemon=True).start()

    def start_download_watcher(self):
        """Auto-imports .tttl / .tttm files that the web portal drops into ~/Downloads."""
        def watch_loop():
            folder = os.path.join(os.path.expanduser('~'), 'Downloads')
            bad = set()
            while self.running:
                time.sleep(1.0)
                try:
                    if not os.path.isdir(folder):
                        continue
                    for fn in os.listdir(folder):
                        low = fn.lower()
                        if not low.endswith(('.tttl', '.tttm')):
                            continue
                        src = os.path.join(folder, fn)
                        try:
                            key = (src, os.path.getmtime(src))
                            if key in bad:
                                continue
                            time.sleep(0.2)
                            with open(src, 'r', encoding='utf-8-sig') as f:
                                content = f.read()
                            try:
                                if low.endswith('.tttl'):
                                    d = text_to_data(content)
                                    dest, out, music = os.path.join(LEVELS_DIR, safe_name(d['name']) + '.tttl'), data_to_text(d), False
                                else:
                                    d = text_to_song(content)
                                    dest, out, music = os.path.join(MUSIC_DIR, safe_name(d['name']) + '.tttm'), song_to_text(d), True
                                os.makedirs(os.path.dirname(dest), exist_ok=True)
                                with open(dest, 'w', encoding='utf-8') as fo:
                                    fo.write(out)
                                os.remove(src)
                                self.import_q.append(('watch', d['name'], music))
                            except Exception:
                                bad.add(key)      # not one of ours / broken: don't retry every second
                        except Exception:
                            pass
                except Exception:
                    pass

        threading.Thread(target=watch_loop, daemon=True).start()

    def toast_asset_imported(self, asset_name, is_music=False):
        self.sfx('clear')
        prefix = 'TRACK IMPORTED: ' if is_music else 'MAP IMPORTED: '
        self.toast = [prefix + self._pstr(asset_name, 'UNTITLED', 30), 180]
        if self.state == 'custom':
            self.open_custom()
        elif self.state == 'music' and self.mm and getattr(self.mm, 'modal', None) == 'open':
            self.mm.files = list_files(MUSIC_DIR, '.tttm')

    # ---------- account / publishing ----------
    def portal_session(self):
        p = self.save.get('portal') if isinstance(self.save.get('portal'), dict) else {}
        return p.get('user') or '', p.get('token') or ''

    def _portal_http(self, method, path, body=None, raw=None, params=None, token=None, timeout=15):
        """One JSON request to the portal API. HTTP errors raise RuntimeError(code, message)."""
        import urllib.request
        import urllib.parse
        import urllib.error
        url = self.PORTAL_API + path
        if params:
            url += '?' + urllib.parse.urlencode(params)
        headers, data = dict(self.PORTAL_UA), None
        if body is not None:
            data = json.dumps(body).encode('utf-8')
            headers['Content-Type'] = 'application/json'
        elif raw is not None:
            data = raw
            headers['Content-Type'] = 'application/octet-stream'
        if token:
            headers['X-Turning-Tower-Token'] = token   # (Authorization is reserved by Websim)
        rq = urllib.request.Request(url, data=data, headers=headers, method=method)
        try:
            with urllib.request.urlopen(rq, timeout=timeout) as resp:
                txt = resp.read().decode('utf-8', 'replace')
        except urllib.error.HTTPError as ex:
            msg = ''
            try:
                j = json.loads(ex.read().decode('utf-8', 'replace'))
                if isinstance(j, dict):
                    msg = j.get('detail') or j.get('message') or j.get('error') or ''
                    msg = msg if isinstance(msg, str) else json.dumps(msg)
            except Exception:
                pass
            raise RuntimeError(ex.code, msg)
        return json.loads(txt) if txt.strip() else {}

    def _portal_err(self, ex, authed=False):
        """(text for the toast, http status or 0)"""
        import urllib.error
        if isinstance(ex, RuntimeError) and len(ex.args) == 2:
            code, msg = ex.args
            if code == 401:
                return ('SESSION EXPIRED' if authed else 'WRONG USERNAME OR PASSWORD'), 401
            return self._pstr(msg or ('SERVER ERROR %d' % code), n=44), code
        if isinstance(ex, (urllib.error.URLError, OSError)):
            return 'CANNOT REACH THE PORTAL SERVER', 0
        if isinstance(ex, (ValueError, KeyError, TypeError, AttributeError)):
            return 'UNEXPECTED REPLY FROM SERVER', 0
        return 'PORTAL ERROR', 0

    def portal_login(self, user, pw):
        if self.portal_busy:
            return
        self.portal_busy = True
        self.toast = ['SIGNING IN...', 600]
        q = self.import_q

        def worker():
            try:
                j = self._portal_http('POST', '/auth/login', body={'username': user, 'password': pw})
                tok = j.get('access_token') if isinstance(j, dict) else None
                if not tok:
                    raise ValueError('no token')
                q.append(('login_ok', user, tok))
            except Exception as ex:
                q.append(('login_fail',) + self._portal_err(ex))

        threading.Thread(target=worker, daemon=True).start()

    def portal_logout(self):
        _, tok = self.portal_session()
        self.save['portal'] = {}
        self.write_save()
        self.toast = ['SIGNED OUT', 150]
        self.sfx('back')
        if tok:
            def worker():
                try:
                    self._portal_http('POST', '/auth/logout', token=tok, body={})
                except Exception:
                    pass
            threading.Thread(target=worker, daemon=True).start()

    def portal_publish(self, kind, fname, desc):
        """Uploads a local level / song file, then publishes it under the signed-in account."""
        if self.portal_busy:
            return
        user, tok = self.portal_session()
        if not tok:
            self.toast = ['SIGN IN FIRST', 150]
            return
        music = kind == 'music'
        try:
            with open(os.path.join(MUSIC_DIR if music else LEVELS_DIR, fname), 'rb') as f:
                raw = f.read()
            text = raw.decode('utf-8-sig')
            parsed = text_to_song(text) if music else text_to_data(text)
            name = str(parsed['name'])
        except Exception:
            self.toast = ['THAT FILE IS BROKEN', 150]
            return
        self.portal_busy = True
        self.toast = ['PUBLISHING ' + kind.upper() + '...', 900]
        q = self.import_q

        def worker():
            try:
                up = self._portal_http('POST', '/upload', raw=raw, token=tok,
                                       params={'kind': kind, 'file_name': fname})
                uid = up.get('id', up.get('uploadId')) if isinstance(up, dict) else None
                if uid is None:
                    raise ValueError('no upload id')
                body = {'uploadId': uid, 'name': name}
                if not music:
                    body['description'] = desc or 'Made in-game'
                    body['tags'] = []
                self._portal_http('POST', '/music/publish' if music else '/levels/publish', body=body, token=tok)
                q.append(('pub_ok', name, music))
            except Exception as ex:
                q.append(('pub_fail',) + self._portal_err(ex, authed=True))

        threading.Thread(target=worker, daemon=True).start()

    def portal_event(self, kind, a, b):
        """Results of login / publish worker threads (called from update)."""
        self.portal_busy = False
        if kind == 'login_ok':
            self.save['portal'] = {'user': a, 'token': b}
            self.write_save()
            self.sfx('clear')
            self.toast = ['SIGNED IN AS ' + self._pstr(a, '', 16), 180]
        elif kind == 'pub_ok':
            self.sfx('clear')
            self.toast = ['PUBLISHED: ' + self._pstr(a, '', 24), 200]
            if self.state == 'online_browser':
                self.fetch_portal_page()
        else:                                   # login_fail / pub_fail
            self.sfx('back')
            if kind == 'pub_fail' and b == 401:
                self.save['portal'] = {}
                self.write_save()
                self.toast = ['SESSION EXPIRED - SIGN IN AGAIN', 200]
            else:
                self.toast = [a, 200]

    def portal_close(self):
        self.portal_edit = None
        self.portal_mode = 'browse'
        self.chars = []
        self.sfx('back')
        self.set_state('title')
        if 'LEVEL PORTAL' in TITLE_ITEMS:
            self.menu = TITLE_ITEMS.index('LEVEL PORTAL')

    def upd_online_browser(self):
        self.portal_poll()
        ev = self.events

        # ---- text boxes: search / username / password / description ----
        if self.portal_edit is not None:
            e = self.portal_edit
            kind = e.get('kind', 'search')
            lim = {'search': 24, 'user': 32, 'pass': 64, 'desc': 60}.get(kind, 24)
            for ch in self.chars:
                if len(e['buf']) < lim:
                    e['buf'] += ch
            self.chars = []
            if 'backspace' in ev:
                e['buf'] = e['buf'][:-1]
            if 'return' in ev or 'kp_enter' in ev:
                self.portal_edit = None
                self.sfx('ok')
                if kind == 'search':
                    self.portal_search = e['buf'].strip()
                    self.fetch_portal_page()
                elif kind == 'user':
                    if e['buf'].strip():
                        self.portal_login_user = e['buf'].strip()
                        self.portal_edit = dict(kind='pass', buf='')
                elif kind == 'pass':
                    if e['buf']:
                        self.portal_login(self.portal_login_user, e['buf'])
                elif kind == 'desc':
                    self.portal_mode = 'browse'
                    self.portal_publish('level', self.portal_pub_pick, e['buf'].strip())
            elif 'escape' in ev:
                self.portal_edit = None
                self.sfx('back')
            return

        # ---- pick a local file to publish ----
        if self.portal_mode == 'publish':
            files = self.portal_pub_files
            n = len(files)
            if n and self.pressed(K_UPK):
                self.portal_pub_i = (self.portal_pub_i - 1) % n
                self.sfx('menu')
            if n and self.pressed(K_DOWNK):
                self.portal_pub_i = (self.portal_pub_i + 1) % n
                self.sfx('menu')
            if self.pressed(K_BACK):
                self.portal_mode = 'browse'
                self.sfx('back')
            elif self.pressed(K_OK) and n:
                self.portal_pub_pick = files[self.portal_pub_i]
                self.sfx('ok')
                if self.portal_pub_kind == 'music':
                    self.portal_mode = 'browse'
                    self.portal_publish('music', self.portal_pub_pick, '')
                else:
                    self.portal_edit = dict(kind='desc', buf='')
                    self.chars = []
            return

        n = len(self.portal_items)
        if self.pressed(K_LEFTK) or self.pressed(K_RIGHTK):
            self.portal_tab = (self.portal_tab + (1 if self.pressed(K_RIGHTK) else -1)) % 3
            self.sfx('menu')
            self.fetch_portal_page()
            return
        if n and self.pressed(K_UPK):
            self.portal_i = (self.portal_i - 1) % n
            self.sfx('menu')
        if n and self.pressed(K_DOWNK):
            self.portal_i = (self.portal_i + 1) % n
            self.sfx('menu')
        if 'f' in ev or 'slash' in ev:
            self.portal_edit = dict(kind='search', buf=self.portal_search)
            self.chars = []
            self.sfx('ok')
            return
        if 'x' in ev and self.portal_search:
            self.portal_search = ''
            self.sfx('back')
            self.fetch_portal_page()
            return
        if 'r' in ev:
            self.sfx('menu')
            self.fetch_portal_page()
            return
        if 'l' in ev:                                   # sign in / sign out
            if self.portal_session()[1]:
                self.portal_logout()
            elif not self.portal_busy:
                self.portal_edit = dict(kind='user', buf='')
                self.chars = []
                self.sfx('ok')
            return
        if 'p' in ev:                                   # publish a local level / song
            if not self.portal_session()[1]:
                self.toast = ['SIGN IN TO PUBLISH', 150]
                self.portal_edit = dict(kind='user', buf='')
                self.chars = []
                return
            music = self.portal_tab == 2
            files = list_files(MUSIC_DIR if music else LEVELS_DIR, '.tttm' if music else '.tttl')
            if not files:
                self.toast = ['NO SONG FILES FOUND' if music else 'NO LEVEL FILES FOUND', 150]
                return
            self.portal_pub_kind = 'music' if music else 'level'
            self.portal_pub_files, self.portal_pub_i = files, 0
            self.portal_mode = 'publish'
            self.sfx('ok')
            return
        if 'o' in ev:                                   # open the web portal in a real browser
            try:
                import webbrowser
                open_url(self.PORTAL_WEB)
                self.toast = ['PORTAL OPENED IN BROWSER', 150]
            except Exception:
                self.toast = ['COULD NOT OPEN BROWSER', 150]
            return
        if self.pressed(K_BACK):
            self.portal_close()
        elif self.pressed(K_OK) and n and not self.portal_loading:
            item = self.portal_items[min(self.portal_i, n - 1)]
            item_id = item.get('id', item.get('_id'))
            if item_id is not None:
                self.sfx('ok')
                self.download_portal_asset(item_id, 'music' if self.portal_tab == 2 else 'level')
            else:
                self.toast = ['THIS RECORD HAS NO ID', 120]

    def _draw_portal_footer(self, msg):
        VW, VH = self.VW, self.VH
        self.rect(0, VH - 14, VW, 14, C_PANEL)
        self.rect(0, VH - 14, VW, 1, C_EDGE)
        self.text(msg, VW / 2.0, VH - 10, C_FAINT, 1, 'c', shadow=False)
        if self.toast:
            self.text(self._pstr(self.toast[0], '', 70), VW / 2.0, VH - 26, C_GOLD, 1, 'c')

    def _draw_portal_editbox(self):
        if self.portal_edit is None:
            return
        VW, VH = self.VW, self.VH
        kind = self.portal_edit.get('kind', 'search')
        label = {'search': 'SEARCH THE ARCHIVE', 'user': 'ACCOUNT USERNAME', 'pass': 'ACCOUNT PASSWORD',
                 'desc': 'LEVEL DESCRIPTION (OPTIONAL)'}.get(kind, 'TYPE HERE')
        shown = self._pstr(self.portal_edit['buf'], '') if kind != 'pass' else '*' * len(self.portal_edit['buf'])
        if kind != 'pass':
            shown = ''.join(ch if ' ' <= ch <= '~' else ' ' for ch in str(self.portal_edit['buf'])).upper()
        shown = shown[-40:]
        bw, bh = 220, 44
        bx, by = (VW - bw) / 2.0, VH / 2.0 - 22
        self.panel(bx, by, bw, bh)
        self.text(label, bx + 8, by + 6, C_GOLD)
        cur = '_' if (self.t // 20) % 2 == 0 else ' '
        self.text(shown + cur, bx + 8, by + 20, C_TEXT)
        self.text('ENTER OK  ESC CANCEL', bx + bw - 8, by + bh - 9, C_FAINT, 1, 'r', shadow=False)

    def _draw_portal_publish(self, x, y, w, h):
        music = self.portal_pub_kind == 'music'
        self.text('PUBLISH A TRACK' if music else 'PUBLISH A LEVEL', x + 8, y + 4, C_GOLD, 1, shadow=False)
        self.text('AS ' + self._pstr(self.portal_session()[0], 'ACCOUNT', 16), x + w - 8, y + 4, C_CYAN, 1, 'r', shadow=False)
        self.rect(x + 1, y + 13, w - 2, 1, C_EDGE)
        files, n = self.portal_pub_files, len(self.portal_pub_files)
        off = max(0, min(self.portal_pub_i - 5, n - 7))
        for i, fn in enumerate(files[off:off + 7]):
            sel = off + i == self.portal_pub_i
            yy = y + 18 + i * 14
            if sel:
                self.rect(x + 3, yy - 2, w - 6, 12, '#1d1840')
                self.text('>', x + 6, yy, C_GOLD)
            self.text(self._pstr(os.path.splitext(fn)[0], 'UNTITLED', 40), x + 16, yy, C_TEXT if sel else C_DIM)
        self.text('%d/%d' % (self.portal_pub_i + 1, n), x + w - 6, y + h - 8, C_FAINT, 1, 'r', shadow=False)

    def draw_online_browser(self):
        VW, VH = self.VW, self.VH
        self.rect(0, 0, VW, 16, C_PANEL)
        self.rect(0, 15, VW, 1, C_EDGE)
        self.text('TOWER PORTAL ARCHIVE', 8, 4, C_GOLD, 1, shadow=False)
        user = self.portal_session()[0] if self.portal_session()[1] else ''
        self.text(('SIGNED IN: ' + self._pstr(user, '', 12)) if user else 'GUEST', VW - 8, 4,
                  '#7dffa0' if user else C_FAINT, 1, 'r', shadow=False)
        if self.portal_search:
            self.text('SEARCH: ' + self._pstr(self.portal_search, '', 20), 100, 4, C_CYAN, 1, shadow=False)

        w = min(290.0, VW - 12.0)
        h = 138
        x, y = (VW - w) / 2.0, 22
        self.panel(x, y, w, h)

        if self.portal_mode == 'publish':
            self._draw_portal_publish(x, y, w, h)
            self._draw_portal_footer('ENTER: PUBLISH  ESC: CANCEL')
            self._draw_portal_editbox()
            return

        tw = w / 3.0
        for i, title in enumerate(self.PORTAL_TABS):
            tx = x + 6 + i * tw
            active = i == self.portal_tab
            self.text(title, tx, y + 4, C_GOLD if active else C_FAINT, 1, shadow=False)
            if active:
                self.rect(tx, y + 11, len(title) * 4 - 1, 1, C_GOLD)
        self.rect(x + 1, y + 13, w - 2, 1, C_EDGE)

        n = len(self.portal_items)
        if self.portal_msg:
            msg = self.portal_msg
            if self.portal_loading:
                msg += '.' * ((self.t // 15) % 4)
            for k, ln in enumerate(msg.split('\n')):
                self.text(ln, VW / 2.0, y + 56 + k * 10, C_DIM if k == 0 else C_FAINT, 1, 'c')
        else:
            self.text('%d/%d' % (self.portal_i + 1, n), x + w - 6, y + h - 8, C_FAINT, 1, 'r', shadow=False)
            off = max(0, min(self.portal_i - 3, n - 4))
            for i, item in enumerate(self.portal_items[off:off + 4]):
                idx = off + i
                sel = idx == self.portal_i
                yy = y + 18 + i * 28
                if sel:
                    self.rect(x + 3, yy - 1, w - 6, 26, '#1d1840')
                    self.text('>', x + 6, yy + 6, C_GOLD)
                name = self._pstr(item.get('name', item.get('title')), 'UNTITLED', 22)
                author = 'BY ' + self._pstr(item.get('author', item.get('creator', item.get('username'))), 'UNKNOWN', 14)
                self.text(name, x + 16, yy, C_TEXT if sel else C_DIM)
                self.text(author, x + w - 8, yy + 9 if self.portal_tab != 2 else yy, C_FAINT, 1, 'r')
                dl = self._pstr(item.get('download_count', item.get('downloads', 0)), '0', 8)
                if self.portal_tab in (0, 1):
                    try:
                        tn = THEMES[int(item.get('theme', 0)) % len(THEMES)]['name']
                    except (TypeError, ValueError):
                        tn = THEMES[0]['name']
                    self.text(tn, x + w - 8, yy, C_PURPLE, 1, 'r')
                    desc = self._pstr(item.get('description'), 'NO DESCRIPTION', 36)
                    self.text(desc, x + 16, yy + 9, C_TEXT if sel else C_FAINT)
                    self.text('DOWNLOADS: ' + dl, x + 16, yy + 17, C_FAINT)
                else:
                    self.text('BPM: %s (%s)' % (self._pstr(item.get('bpm', 100), '100', 5),
                                                self._pstr(item.get('scale', 'minor'), 'MINOR', 10)),
                              x + w - 8, yy + 9, C_PURPLE, 1, 'r')
                    self.text('CUSTOM CHIPTUNE TRACK', x + 16, yy + 9, C_TEXT if sel else C_FAINT)
                    self.text('DOWNLOADS: ' + dl, x + 16, yy + 17, C_FAINT)

        self._draw_portal_footer('ENTER: GET  F: SEARCH  L: %s  P: PUBLISH  R: RETRY  ESC: BACK'
                                 % ('SIGN OUT' if user else 'SIGN IN'))
        self._draw_portal_editbox()

    def update(self):
        if not self.running:
            return
        while self.import_q:
            kind, name, is_music = self.import_q.pop(0)
            if kind in ('login_ok', 'login_fail', 'pub_ok', 'pub_fail'):
                self.portal_event(kind, name, is_music)
                continue
            if kind == 'fail':
                self.toast = [name, 150]
            else:
                self.toast_asset_imported(name, is_music)
            if kind in ('ok', 'fail'):
                self.portal_dl_busy = False
        super().update()
        if self.toast and self.state in ('title', 'online_browser', 'custom', 'options', 'select', 'howto',
                                         'music', 'editor', 'story_menu'):
            self.toast[1] -= 1
            if self.toast[1] <= 0:
                self.toast = None
        self.mev = []
        self.chars = []

    def load_save(self):
        d = super().load_save()
        d.setdefault('story', {})
        d['opts'].setdefault('theme_song', None)
        return d

    def skin_ok(self, i):
        return self.total_stars() >= SKINS[i][1] or i in self.save.get('story', {}).get('cloaks', [0])

    def apply_theme_song(self, restart=True):
        self.theme_song = None
        fn = self.save['opts'].get('theme_song')
        if fn:
            try:
                with open(os.path.join(MUSIC_DIR, fn), 'r', encoding='utf-8') as f:
                    self.theme_song = text_to_song(f.read())
            except Exception:
                self.save['opts']['theme_song'] = None
        if restart and self.running:
            self.audio.want = None
            self.audio.stop_music()
            if self.state in ('title', 'options'):
                self.bgm('title', 1, 'title')

    def bgm(self, key, seed, mood):
        if not self.running: 
            return
        lvl = getattr(self, 'lvl', None)
        if key.startswith('w') and self.mode in ('custom', 'test') and lvl is not None and getattr(lvl, 'song', None):
            self.audio.music_song('lvl', lvl.song)
        elif getattr(self, 'theme_song', None) and not key.startswith('boss'):
            self.audio.music_song('theme', self.theme_song)
        else:
            self.audio.music(key, seed, mood)

    def make_level(self, spec):
        if isinstance(spec, dict) and spec.get('fmt') == 'TTTL':
            return GridLevel(spec)
        return Level(spec)

    def title_items(self):
        return list(TITLE_ITEMS)

    def upd_title(self):
        self.menu_nav(len(TITLE_ITEMS))
        if self.pressed(K_OK):
            self.sfx('ok')
            m = self.menu
            it = TITLE_ITEMS[m]
            
            if it == 'LEVEL PORTAL':
                self.goto(self.open_level_portal)
            elif it == 'STORY MODE':
                self.goto(lambda: (self.set_state('story_menu'), setattr(self, 'menu_msg', '')))
            elif it == 'CAMPAIGN':
                i = min(self.save['unlocked'], len(LEVELS)) - 1
                self.run_tot = dict(frames=0, deaths=0, souls=0)
                self.goto(lambda: self.start_campaign(max(0, i)))
            elif it == 'LEVEL SELECT':
                self.goto(lambda: (self.set_state('select'), setattr(self, 'sel', 0)))
            elif it == 'ENDLESS TOWER':
                self.goto(self.start_endless)
            elif it == 'DAILY TOWER':
                self.goto(self.start_daily)
            elif it == 'LEVEL EDITOR':
                self.goto(lambda: self.open_editor())
            elif it == 'MY LEVELS':
                self.goto(self.open_custom)
            elif it == 'MUSIC MAKER':
                self.goto(self.open_music)
            elif it == 'OPTIONS':
                self.goto(lambda: self.set_state('options'))
            elif it == 'HOW TO PLAY':
                self.goto(lambda: self.set_state('howto'))
            elif it == 'QUIT':
                self.quit()

    def draw_title_menu(self):
        x = 14
        y = 46
        for i, it in enumerate(TITLE_ITEMS):
            sel = i == self.menu
            if sel:
                self.text('>', x - 7 + (1 if (self.t // 15) % 2 else 0), y, C_GOLD)
            col = C_GOLD if (i == 0 and not sel) else (C_TEXT if sel else C_DIM)
            self.text(it, x, y, col, 1)
            y += 9
        e = self.save['endless']
        if e['score']:
            self.text('ENDLESS BEST %d' % e['score'], self.VW - 8, 6, C_FAINT, 1, 'r')
        self.text('STARS %d' % self.total_stars(), self.VW - 8, 13, C_GOLD, 1, 'r')
        self.text('UP DOWN: CHOOSE   ENTER: OK', 8, self.VH - 10, C_FAINT, 1)
        self.text('GMI GAME JAM 2026', self.VW - 8, self.VH - 10, C_FAINT, 1, 'r')

    def set_cursor(self):
        want = 'arrow' if self.state in MOUSE_STATES else 'none'
        if want != self.cursor:
            self.cursor = want
            try:
                self.canvas.config(cursor=want)
            except Exception:
                pass

    # -- story menu -----------------------------------------------------------------------------------
    def upd_story_menu(self):
        has = bool(self.save['story'].get('started'))
        items = (['CONTINUE', 'NEW GAME', 'BACK'] if has else ['NEW GAME', 'BACK'])
        self.menu_nav(len(items))
        if self.pressed(K_BACK):
            self.goto(self.go_title)
        elif self.pressed(K_OK):
            it = items[self.menu]
            self.sfx('ok')
            if it == 'CONTINUE':
                self.goto(self.story_continue)
            elif it == 'NEW GAME':
                if has and self.menu_msg != 'sure':
                    self.menu_msg = 'sure'
                else:
                    self.goto(self.story_new_game)
            else:
                self.goto(self.go_title)
        if self.pressed(K_UPK | K_DOWNK):
            self.menu_msg = ''

    def draw_story_menu(self):
        VW = self.VW
        st = self.save['story']
        has = bool(st.get('started'))
        items = (['CONTINUE', 'NEW GAME', 'BACK'] if has else ['NEW GAME', 'BACK'])
        w, h = 200, 126
        x, y = (VW - w) / 2.0, 22
        self.panel(x, y, w, h)
        self.wave_text('STORY MODE', VW / 2.0, y + 6, 2, C_GOLD, 1.2, 0.08)
        self.text('THE TOWER HAS STOPPED TURNING.', VW / 2.0, y + 26, C_DIM, 1, 'c')
        if has:
            self.text('GEARS %d/6   HEARTS %d   SOULS %d' % (len(st['gears']), st['hearts'], st['souls']),
                      VW / 2.0, y + 38, C_CYAN, 1, 'c')
            self.text('PAGES %d/12   TIME %s' % (len(st['pages']), fmt_time(st['frames'] / 60.0)), VW / 2.0, y + 47, C_DIM, 1, 'c')
        yy = y + 64
        for i, it in enumerate(items):
            sel = i == self.menu
            if sel:
                self.text('>', x + 62, yy, C_GOLD)
            label = it
            if it == 'NEW GAME' and has and self.menu_msg == 'sure' and sel:
                label = 'SURE? ERASES SAVE'
            self.text(label, x + 72, yy, C_TEXT if sel else C_DIM)
            yy += 11
        self.text('ESC: BACK', VW / 2.0, y + h - 9, C_FAINT, 1, 'c')

    # -- editor / music maker / custom levels ---------------------------------------------------------------
    def open_editor(self, data=None, path=None):
        self.mode = 'edit'
        self.editor = Editor(self, data, path)
        self.state = 'editor'
        self.mev = []

    def leave_editor(self):
        self.editor = None
        self.goto(self.go_title)

    def open_music(self):
        self.mode = 'music'
        self.mm = MusicMaker(self)
        self.state = 'music'

    def leave_music(self):
        self.mm = None
        self.audio.want = None
        self.goto(self.go_title)

    def upd_editor(self):
        if self.editor is None:
            self.go_title()
            return
        self.editor.update()

    def upd_music(self):
        if self.mm is None:
            self.go_title()
            return
        self.mm.update()

    def start_test(self, ed):
        self.test_editor = ed
        data = ed.to_data()

        def go():
            self.mode = 'test'
            self.begin_level(data)
            self.state = 'play'
        self.goto(go)

    def back_to_editor(self):
        self.mode = 'edit'
        self.state = 'editor'
        self.lvl = None

    def open_custom(self):
        self.custom_files = list_files(LEVELS_DIR, '.tttl')
        self.custom_i = min(self.custom_i, max(0, len(self.custom_files) - 1))
        self.state = 'custom'
        self.mode = 'custom_list'

    def custom_info(self, f):
        if f not in self.custom_meta:
            try:
                with open(os.path.join(LEVELS_DIR, f), 'r', encoding='utf-8') as fh:
                    d = text_to_data(fh.read())
                self.custom_meta[f] = (d['name'], d['author'], '%dX%d' % (len(d['rows'][0]), len(d['rows'])),
                                       THEMES[d['theme']]['name'], bool(d.get('music')))
            except Exception:
                self.custom_meta[f] = ('BROKEN FILE', '?', '', '', False)
        return self.custom_meta[f]

    def upd_custom(self):
        n = len(self.custom_files)
        ev = self.events
        if n:
            if self.pressed(K_UPK):
                self.custom_i = (self.custom_i - 1) % n
            if self.pressed(K_DOWNK):
                self.custom_i = (self.custom_i + 1) % n
        if self.pressed(K_BACK):
            self.goto(self.go_title)
            return
        if 'n' in ev:
            self.goto(lambda: self.open_editor())
            return
        if 'i' in ev:
            self.pick_file(('.tttl',), self._import_custom_level, 'IMPORT LEVEL')
            return
        if not n:
            return
        f = self.custom_files[self.custom_i]
        path = os.path.join(LEVELS_DIR, f)
        if 'delete' in ev:
            try:
                os.remove(path)
                self.custom_files = list_files(LEVELS_DIR, '.tttl')
                self.custom_i = 0
            except Exception:
                pass
        elif 'e' in ev:
            try:
                with open(path, 'r', encoding='utf-8') as fh:
                    d = text_to_data(fh.read())
                self.goto(lambda: self.open_editor(d, path))
            except Exception:
                pass
        elif self.pressed(K_OK):
            try:
                with open(path, 'r', encoding='utf-8') as fh:
                    d = text_to_data(fh.read())
                self.sfx('ok')

                def go():
                    self.mode = 'custom'
                    self.begin_level(d)
                self.goto(go)
            except Exception:
                self.sfx('back')

    def draw_custom(self):
        VW = self.VW
        w, h = 260, 150
        x, y = (VW - w) / 2.0, 12
        self.panel(x, y, w, h)
        self.text('MY LEVELS', VW / 2.0, y + 5, C_GOLD, 2, 'c')
        if not self.custom_files:
            self.text('NO LEVELS YET', VW / 2.0, y + 50, C_DIM, 1, 'c')
            self.text('PRESS N TO MAKE ONE IN THE EDITOR', VW / 2.0, y + 60, C_FAINT, 1, 'c')
            self.text('OR I TO IMPORT A .TTTL FILE', VW / 2.0, y + 69, C_FAINT, 1, 'c')
        off = max(0, self.custom_i - 8)
        for i, f in enumerate(self.custom_files[off:off + 10]):
            sel = off + i == self.custom_i
            name, author, size, theme, music = self.custom_info(f)
            yy = y + 20 + i * 11
            if sel:
                self.rect(x + 3, yy - 2, w - 6, 11, '#1d1840')
                self.text('>', x + 6, yy, C_GOLD)
            self.text(name, x + 16, yy, C_TEXT if sel else C_DIM)
            self.text('BY ' + author, x + 120, yy, C_FAINT)
            self.text(size + (' +MUSIC' if music else ''), x + w - 6, yy, C_FAINT, 1, 'r')
        self.text('ENTER PLAY  E EDIT  N NEW  I IMPORT  DEL DELETE  ESC BACK', VW / 2.0, y + h + 4, C_FAINT, 1, 'c')

    # -- options (adds theme song) ---------------------------------------------------------------------------------
    def upd_options(self):
        o = self.save['opts']
        self.menu_nav(6)
        step = (1 if self.pressed(K_RIGHTK) else 0) - (1 if self.pressed(K_LEFTK) else 0)
        m = self.menu
        changed = False
        if step or self.pressed(K_OK):
            if m == 0:
                o['music'] = max(0, min(10, o['music'] + (step or 1)))
                self.audio.mvol = o['music']
                self.audio.set_volumes()
                changed = True
            elif m == 1:
                o['sfx'] = max(0, min(10, o['sfx'] + (step or 1)))
                self.audio.svol = o['sfx']
                changed = True
            elif m == 2:
                o['shake'] = not o['shake']
                changed = True
            elif m == 3:
                n = len(SKINS)
                for k in range(1, n + 1):
                    c = (o['skin'] + (step or 1) * k) % n
                    if self.skin_ok(c):
                        o['skin'] = c
                        break
                changed = True
            elif m == 4:
                names = [None] + list_files(MUSIC_DIR, '.tttm')
                cur = o.get('theme_song')
                i = names.index(cur) if cur in names else 0
                o['theme_song'] = names[(i + (step or 1)) % len(names)]
                self.apply_theme_song()
                changed = True
            elif m == 5 and self.pressed(K_OK):
                self.write_save()
                self.goto(self.go_title)
                self.sfx('back')
                return
            if changed:
                self.sfx('ok')
        if self.pressed(K_BACK):
            self.write_save()
            self.sfx('back')
            self.goto(self.go_title)

    def draw_options(self):
        VW = self.VW
        o = self.save['opts']
        w, h = 210, 134
        x, y = (VW - w) / 2.0, 20
        self.panel(x, y, w, h)
        self.text('OPTIONS', VW / 2.0, y + 6, C_GOLD, 2, 'c')
        sk = SKINS[o['skin']]
        ts = o.get('theme_song')
        rows = ['MUSIC     < %d >' % o['music'], 'SOUND FX  < %d >' % o['sfx'],
                'SHAKE     < %s >' % ('ON' if o['shake'] else 'OFF'), 'CLOAK     < %s >' % sk[0],
                'THEME     < %s >' % (ts[:-5].upper() if ts else 'DEFAULT'), 'BACK']
        yy = y + 24
        for i, r in enumerate(rows):
            sel = i == self.menu
            if sel:
                self.text('>', x + 8, yy, C_GOLD)
            self.text(r, x + 18, yy, C_TEXT if sel else C_DIM)
            yy += 11
        self.img(self.assets.player('stand', 1, DOWN, o['skin']), x + w - 28, y + 54)
        nxt = [s for s in SKINS if s[1] > self.total_stars()]
        if nxt:
            self.text('NEXT CLOAK AT %d STARS' % nxt[0][1], VW / 2.0, y + 92, C_FAINT, 1, 'c')
        st = self.save['stats']
        self.text('DEATHS %d   SOULS %d' % (st['deaths'], st['souls']), VW / 2.0, y + 102, C_DIM, 1, 'c')
        self.text('TIME %s   STARS %d' % (fmt_time(st['frames'] / 60.0), self.total_stars()), VW / 2.0, y + 111, C_DIM, 1, 'c')
        self.text('MAKE SONGS IN THE MUSIC MAKER', VW / 2.0, y + h - 9, C_FAINT, 1, 'c')

    # -- game-flow overrides -------------------------------------------------------------------------------------------
    def handle_events(self, ev):
        if self.mode == 'story':
            self.story_soul_events(ev)
        super().handle_events(ev)

    def on_death(self, manual=False):
        super().on_death(manual)
        if self.mode == 'story':
            self.st['deaths'] += 1

    def on_door(self):
        lvl, sim = self.lvl, self.sim
        if self.mode == 'story':
            if self.loc in REGION:
                self.sfx('clear')
                self.burst(lvl.door[0] + 8, lvl.door[1] + 16, THEMES[lvl.theme]['accent'], 30, 2.4, 40)
                loc = 'a' + self.loc[1:]
                self.goto(lambda: self.story_enter(loc))
            return
        if self.mode == 'test':
            self.sfx('clear')
            self.toast = ['LEVEL CLEARED!', 200]
            self.goto(self.back_to_editor)
            return
        if self.mode == 'custom':
            secs = self.stats['frames'] / 60.0
            total, got = len(lvl.souls), self.stats['souls']
            stars = 1 + (1 if got >= total else 0) + (1 if secs <= lvl.par else 0)
            self.result = dict(secs=secs, got=got, total=total, stars=stars, deaths=self.stats['deaths'], new=False, bonus=0)
            self.unlock_msg = None
            self.sfx('clear')
            self.burst(lvl.door[0] + 8, lvl.door[1] + 16, THEMES[lvl.theme]['accent'], 30, 2.4, 40)
            self.goto(lambda: self.set_state('clear'))
            return
        super().on_door()

    def upd_clear(self):
        if self.mode == 'custom':
            if self.pressed(K_OK) or self.pressed(K_BACK):
                self.sfx('ok')
                self.goto(self.open_custom)
            return
        super().upd_clear()

    def draw_intro(self):
        if self.mode != 'custom':
            return super().draw_intro()
        VW, VH, t = self.VW, self.VH, self.t
        lvl = self.lvl
        T = THEMES[lvl.theme]
        self.rect(0, 0, VW, VH, '#06050c')
        mx, my = VW / 2.0, VH / 2.0
        for k, (rad, n, spd) in enumerate(RINGS):
            for i in range(n):
                a = t * 0.01 * spd + i * 2 * math.pi / n
                self.rect(mx + math.cos(a) * rad * 1.3, my + math.sin(a) * rad * 0.7, 1, 1,
                          T['ring'][1] if i % 5 == 0 else T['ring'][0])
        self.text(T['name'], mx, my - 40, T['accent'], 1, 'c')
        self.text('CUSTOM LEVEL', mx, my - 30, C_PURPLE, 2, 'c')
        self.wave_text(lvl.name, mx, my - 12, 2, C_GOLD, 1.2, 0.08)
        self.text(lvl.sub, mx, my + 8, C_TEXT, 1, 'c')
        if self.intro_t > 20 and (t // 25) % 2 == 0:
            self.text('PRESS ENTER', mx, VH - 14, C_FAINT, 1, 'c')

    # -- pause menu (story / test / custom) ---------------------------------------------------------------------------------
    def pause_items(self):
        if self.mode == 'story':
            return ['RESUME', 'JOURNAL', 'TRAVEL' if self.loc == 'hub' else 'RETURN TO CONCOURSE',
                    'SOUND: ' + ('OFF' if self.audio.muted else 'ON'), 'SAVE AND QUIT']
        if self.mode == 'test':
            return ['RESUME', 'RESTART', 'BACK TO EDITOR']
        if self.mode == 'custom':
            return ['RESUME', 'RESTART', 'BACK TO LIST']
        return super().pause_items()

    def upd_pause(self):
        if self.mode not in ('story', 'test', 'custom'):
            return super().upd_pause()
        items = self.pause_items()
        self.menu_nav(len(items))
        if self.pressed(K_BACK):
            self.state = 'play'
            return
        if not self.pressed(K_OK):
            return
        self.sfx('ok')
        it = items[self.menu]
        if it == 'RESUME':
            self.state = 'play'
        elif it == 'RESTART':
            spec = self.lvl.data if hasattr(self.lvl, 'data') else self.lvl.spec
            self.goto(lambda: (self.begin_level(spec), setattr(self, 'state', 'play')))
        elif it == 'BACK TO EDITOR':
            self.goto(self.back_to_editor)
        elif it == 'BACK TO LIST':
            self.goto(self.open_custom)
        elif it == 'JOURNAL':
            self.jr_tab = 0
            self.jr_i = 0
            self.state = 'journal'
        elif it == 'TRAVEL':
            self.tv_i = 0
            self.state = 'travel'
        elif it == 'RETURN TO CONCOURSE':
            rid = self.loc if self.loc in REGION else 'r' + self.loc[1:]
            self.goto(lambda: self.story_enter('hub', rid))
        elif it.startswith('SOUND'):
            self.audio.muted = not self.audio.muted
            self.audio.set_volumes()
        elif it == 'SAVE AND QUIT':
            self.story_save()
            self.goto(self.go_title)

    def draw_pause(self):
        VW, VH = self.VW, self.VH
        items = self.pause_items()
        w, h = 140, 28 + 10 * len(items)
        x, y = (VW - w) / 2.0, (VH - h) / 2.0
        self.panel(x, y, w, h)
        self.text('PAUSED', VW / 2.0, y + 6, C_GOLD, 2, 'c')
        yy = y + 24
        for i, it in enumerate(items):
            sel = i == self.menu
            if sel:
                self.text('>', x + 10, yy, C_GOLD)
            self.text(it, x + 20, yy, C_TEXT if sel else C_DIM)
            yy += 10

    # -- story drawing --------------------------------------------------------------------------------------------------------
    def draw_ents(self, lvl, sim, sx, sy):
        if not lvl.ents:
            return
        A, t = self.assets, self.t
        px = self.sim.x if self.sim else 0
        for e in lvl.ents:
            x = sx(e['x'])
            if x < -24 or x > self.VW + 24:
                continue
            y = sy(e['y'])
            if e['t'] == 'npc':
                self.img(A.npc(e['id'], 1 if px > e['x'] else -1), x, y)
                self.text(NPC_NAMES.get(e['id'], ''), x + 8, y - 7, C_DIM, 1, 'c')
            elif e['t'] == 'warp':
                locked = self.mode == 'story' and self.gate_locked(e['to'])
                self.img(A.door(REGION[e['to']]['theme'], (t // 10) % 2, False), x, y - 16)
                nm = REGION[e['to']]['name'].replace('THE ', '')
                self.text(nm, x + 8, y - 24, C_FAINT if locked else C_TEXT, 1, 'c')
                if locked:
                    self.text('SEALED', x + 8, y - 17, C_RED, 1, 'c')
            elif e['t'] == 'lift':
                self.rect(x + 1, y + 13, 14, 3, '#4d4399')
                self.rect(x + 3, y + 10, 10, 3, '#7d6fd6')
                self.text('LIFT', x + 8, y - 2, C_DIM, 1, 'c')
            if self.near is e and self.state == 'play':
                self.text('E', x + 8, y - 15 - (2 if (t // 15) % 2 else 0), C_GOLD, 1, 'c')

    def draw_world(self):
        super().draw_world()
        if self.mode != 'story':
            return
        lvl, sim, A, t = self.lvl, self.sim, self.assets, self.t
        VW, VH = self.VW, self.VH
        cx, cy = self.camx, self.camy
        sx = lambda wx: lvl.wd(wx - cx) + VW / 2.0
        sy = lambda wy: wy - cy + VH / 2.0
        wx = sx(self.wisp[0])
        self.img(A.orb((t // 12) % 2), wx - 4, sy(self.wisp[1]) - 4)
        for b in self.bolts:
            x, y = sx(b['x']), sy(b['y'])
            self.rect(x - 2, y - 2, 4, 4, C_CYAN)
            self.rect(x - 1, y - 1, 2, 2, '#ffffff')
        bs = self.boss
        if bs:
            for p in bs.projs:
                x, y = sx(p['x']), sy(p['y'])
                r = p['r']
                col = {'fire': '#ff8a2a', 'saw': '#e8e8f8', 'rain': '#8ff7ff'}.get(p['kind'], C_RED)
                self.rect(x - r, y - r, r * 2, r * 2, col)
                if p['kind'] != 'saw':
                    self.rect(x - r + 1, y - r + 1, r * 2 - 2, r * 2 - 2, '#ffffff')
            if bs.vis:
                im = A.boss(bs.sp['kind'], bs.sp['theme'], (t // 12) % 2)
                self.img(im, sx(bs.x) - 20, sy(bs.y) - 20)
                if bs.flash > 0 and bs.flash % 2 == 0:
                    bx, by, bw, bh = bs.box()
                    self.rect(sx(bx), sy(by), bw, bh, '#ffffff')

    def draw_hud(self):
        if self.mode != 'story':
            return super().draw_hud()
        A, st, sim = self.assets, self.st, self.sim
        VW, VH = self.VW, self.VH
        for i in range(self.maxhp()):
            self.img(A.heart(i < self.hp), 6 + i * 9, 5)
        self.img(A.orb(0), 6, 15)
        self.text('%d' % st['souls'], 16, 16, C_CYAN, 1)
        for i, r in enumerate(REGIONS[:6]):
            self.rect(6 + i * 6, 26, 5, 5, THEMES[r['theme']]['accent'] if r['id'] in st['gears'] else '#2a2450')
        if not self.boss:
            nm = self.lvl.name if self.loc != 'hub' else 'THE CONCOURSE'
            self.text(nm, VW / 2.0, 5, C_DIM, 1, 'c')
        x0, y0 = VW - 24, 4
        self.panel(x0, y0, 17, 17)
        for d, (ax, ay) in ((UP, (6, 1)), (DOWN, (6, 11)), (LEFT, (1, 6)), (RIGHT, (11, 6))):
            self.img(A.arrow5(d, DIRCOL[d] if d == sim.eff else '#2a2450'), x0 + ax, y0 + ay)
        if self.has('lantern'):
            self.text('X LANTERN', VW - 8, 24, C_FAINT, 1, 'r')
        if self.toast:
            self.text(self.toast[0], VW / 2.0, 22, C_GOLD, 1, 'c')
        bs = self.boss
        if bs:
            w = 140
            x = (VW - w) / 2.0
            self.rect(x - 1, 13, w + 2, 7, C_EDGE)
            self.rect(x, 14, w, 5, '#1a0a14')
            self.rect(x, 14, w * bs.hp / float(bs.maxhp), 5, C_RED)
            self.text(bs.name, VW / 2.0, 5, C_TEXT, 1, 'c')
            if bs.tele:
                d = bs.tele[0]
                if (self.t // 6) % 2 == 0:
                    self.rect(0, 0, VW, 3, DIRCOL[d])
                    self.rect(0, VH - 3, VW, 3, DIRCOL[d])
                self.img(A.arrow5(d, DIRCOL[d]), VW / 2.0 - 2, 34)
                self.text('GRAVITY SHIFT', VW / 2.0, 42, DIRCOL[d], 1, 'c')
        elif self.near and self.state == 'play' and self.script is None:
            e = self.near
            lab = {'npc': 'E: TALK', 'warp': 'E: ENTER', 'lift': 'E: USE LIFT'}[e['t']]
            self.text(lab, VW / 2.0, VH - 12, C_GOLD, 1, 'c')

    def render(self):
        st = self.state
        if st == 'online_browser':
            self.set_cursor()
            self.canvas.delete('all')
            self.draw_tower_scene(False)
            self.draw_online_browser()
            if self.trans:
                self.draw_shutters()
            return
        if st == 'play' and self.mode == 'story':
            self.set_cursor()
            self.canvas.delete('all')
            if self.script is not None and self.sbg == 'tower':
                self.draw_tower_scene(False)
            elif self.script is not None and self.sbg == 'black':
                self.rect(0, 0, self.VW, self.VH, '#05040a')
            else:
                self.draw_world()
                self.draw_hud()
            if self.script is not None:
                self.draw_dialogue()
            if self.sfade > 0:
                h = self.sfade * self.VH / 2.0 + 0.5
                self.rect(0, 0, self.VW, h, C_SHUTTER)
                self.rect(0, self.VH - h, self.VW, h, C_SHUTTER)
            if self.trans:
                self.draw_shutters()
            return
        if st in ('story_menu', 'custom', 'shop', 'journal', 'travel', 'credits', 'editor', 'music'):
            self.set_cursor()
            self.canvas.delete('all')
            if st == 'editor':
                if self.editor:
                    self.editor.draw()
            elif st == 'music':
                if self.mm:
                    self.mm.draw()
            elif st in ('shop', 'journal', 'travel'):
                self.draw_world()
                self.draw_hud()
                getattr(self, 'draw_' + st)()
            else:
                self.draw_tower_scene(False)
                getattr(self, 'draw_' + st)()
            if self.trans:
                self.draw_shutters()
            return
        self.set_cursor()
        super().render()

    def draw_dialogue(self):
        s = self.say
        if not s:
            return
        VW, VH, A = self.VW, self.VH, self.assets
        who = s['who']
        x, y, w, h = 6, VH - 56, VW - 12, 50
        self.panel(x, y, w, h)
        tx = x + 8
        port = None
        if who in ('MIRA', 'TOCK', 'BRIN', 'COG', 'BELLOWS', 'GHOST'):
            port = (A._port(who.lower()), 36, 30)
        elif who == 'WISP':
            port = (A.port_orb(), 32, 32)
        elif who == 'WANDERER':
            port = (A.port_player(self.save['opts']['skin']), 36, 30)
        else:
            for b in BOSSES.values():
                if b['name'] == who:
                    port = (A.boss(b['kind'], b['theme'], (self.t // 12) % 2), 40, 40)
                    break
        if port:
            self.rect(x + 4, y + 4, 42, 42, '#15112b')
            self.img(port[0], x + 4 + (42 - port[1]) / 2.0, y + 4 + (42 - port[2]) / 2.0)
            tx = x + 54
        col = SPEAKER_COL.get(who, '#d8b4ff')
        nchars = max(10, int((x + w - 8 - tx) / 4.0))
        if who:
            self.text(who, tx, y + 5, col)
            ty = y + 15
        else:
            ty = y + 10
        lines = wrap_text(s['text'], nchars)
        shown = int(s['n'])
        for ln in lines[:4]:
            if shown <= 0:
                break
            self.text(ln[:shown], tx, ty, C_TEXT if who else '#ffe9a0')
            shown -= len(ln) + 1
            ty += 8
        if s['n'] >= len(s['text']) and (self.t // 18) % 2 == 0:
            self.text('>', x + w - 10, y + h - 9, C_GOLD)

    def draw_shop(self):
        VW, VH = self.VW, self.VH
        st = self.st
        w, h = 250, 150
        x, y = (VW - w) / 2.0, 10
        self.panel(x, y, w, h)
        self.text('MIRA\'S SHOP', x + 8, y + 6, '#ff9a4a', 2)
        self.img(self.assets.orb(0), x + w - 50, y + 7)
        self.text('%d' % st['souls'], x + w - 38, y + 8, C_CYAN)
        for i, (k, name, desc, prices) in enumerate(SHOP):
            yy = y + 24 + i * 10
            sel = i == self.shop_i
            if sel:
                self.rect(x + 3, yy - 2, w - 6, 10, '#1d1840')
                self.text('>', x + 6, yy, C_GOLD)
            n = st['buys'].get(k, 0)
            price = prices[n] if n < len(prices) else None
            owned = price is None
            label = name + (' (%d)' % n if k == 'heart' and n else '')
            self.text(label, x + 16, yy, C_FAINT if owned else (C_TEXT if sel else C_DIM))
            if owned:
                self.text('OWNED' if k != 'heart' else 'SOLD OUT', x + w - 8, yy, C_FAINT, 1, 'r')
            else:
                self.text('%d' % price, x + w - 8, yy, C_CYAN if st['souls'] >= price else C_RED, 1, 'r')
        self.text(SHOP[self.shop_i][2], VW / 2.0, y + h - 18, C_DIM, 1, 'c')
        self.text('ENTER BUY   ESC LEAVE', VW / 2.0, y + h - 9, C_FAINT, 1, 'c')

    def draw_travel(self):
        VW, VH = self.VW, self.VH
        w, h = 130, 62
        x, y = (VW - w) / 2.0, (VH - h) / 2.0
        self.panel(x, y, w, h)
        self.text('LIFT', VW / 2.0, y + 6, C_GOLD, 2, 'c')
        for i, nm in enumerate(['UPPER RING', 'MIDDLE RING', 'LOWER RING'][::-1] if False else ['LOWER RING', 'MIDDLE RING', 'UPPER RING']):
            sel = i == self.tv_i
            if sel:
                self.text('>', x + 14, y + 24 + i * 10, C_GOLD)
            self.text(nm, x + 24, y + 24 + i * 10, C_TEXT if sel else C_DIM)

    def draw_journal(self):
        VW, VH = self.VW, self.VH
        st = self.st
        w, h = 270, 160
        x, y = (VW - w) / 2.0, 8
        self.panel(x, y, w, h)
        tabs = ['QUESTS', 'PAGES', 'STATUS']
        for i, tname in enumerate(tabs):
            tx = x + 10 + i * 60
            self.text(tname, tx, y + 6, C_GOLD if i == self.jr_tab else C_FAINT, 1)
            if i == self.jr_tab:
                self.rect(tx, y + 13, len(tname) * 4, 1, C_GOLD)
        yy = y + 22
        stats = dict(souls_total=st['souls_total'], pages=len(st['pages']), gears=len(st['gears']))
        if self.jr_tab == 0:
            for q in QUESTS:
                done = q['id'] in st['quests_done']
                cur = min(q['goal'], stats[q['stat']])
                self.text(q['title'], x + 10, yy, C_FAINT if done else C_TEXT)
                self.text(q['who'], x + 100, yy, SPEAKER_COL.get(q['who'], C_DIM))
                self.text('DONE' if done else '%d/%d' % (cur, q['goal']), x + w - 8, yy, C_GOLD if done else C_CYAN, 1, 'r')
                self.text(q['desc'], x + 10, yy + 7, C_FAINT)
                yy += 17
        elif self.jr_tab == 1:
            self.jr_i = min(self.jr_i, len(PAGES) - 1)
            for i, (title, body) in enumerate(PAGES):
                found = i in st['pages']
                sel = i == self.jr_i
                if sel:
                    self.text('>', x + 6, y + 22 + (i % 12) * 8, C_GOLD)
                self.text(title if found else '???', x + 14, y + 22 + i * 8, C_TEXT if (found and sel) else (C_DIM if found else C_FAINT))
            if self.jr_i in st['pages']:
                for k, ln in enumerate(wrap_text(PAGES[self.jr_i][1], 38)[:9]):
                    self.text(ln, x + 120, y + 24 + k * 9, C_TEXT)
            else:
                self.text('NOT FOUND YET', x + 120, y + 24, C_FAINT)
        else:
            self.text('GEARS', x + 10, yy, C_GOLD)
            for i, r in enumerate(REGIONS[:6]):
                got = r['id'] in st['gears']
                self.rect(x + 50 + i * 14, yy - 1, 10, 8, THEMES[r['theme']]['accent'] if got else '#2a2450')
            yy += 14
            for lab, val in (('HEARTS', st['hearts']), ('SOULS', st['souls']), ('SOULS FOUND', st['souls_total']),
                             ('PAGES', '%d/12' % len(st['pages'])), ('DEATHS', st['deaths']),
                             ('TIME', fmt_time(st['frames'] / 60.0))):
                self.text(lab, x + 10, yy, C_DIM)
                self.text(str(val), x + 110, yy, C_TEXT)
                yy += 9
            yy += 4
            ab = [('lantern', 'SOUL LANTERN (X)'), ('double', 'AIR STEP BOOTS'), ('dash', 'SPARK CLASP (SHIFT)'),
                  ('lantern2', 'BRIGHT WICK'), ('magnet', 'SOUL MAGNET')]
            for key, lab in ab:
                self.text(lab, x + 10, yy, C_CYAN if key in st['ab'] else C_FAINT)
                yy += 8
        self.text('LEFT RIGHT TABS   ESC CLOSE', VW / 2.0, y + h - 9, C_FAINT, 1, 'c')

    def draw_credits(self):
        VW, VH = self.VW, self.VH
        self.rect(0, 0, VW, VH, '#05040a')
        for i, ln in enumerate(CREDITS):
            yy = VH - self.credits_t * 0.5 + i * 14
            if -10 < yy < VH:
                self.text(ln, VW / 2.0, yy, C_GOLD if i == 0 else C_TEXT, 2 if i == 0 else 1, 'c')

    def draw_story_menu_wrapper(self):
        self.draw_story_menu()


# ============================================================================
#  KIVY LAYER  -  everything below replaces what tkinter used to do:
#    drawing (texture atlas + batched meshes), keyboard, touch controls,
#    audio (Kivy SoundLoader), file picking, app lifecycle.
# ============================================================================
IS_MOBILE = TT_MOBILE or kplatform in ('android', 'ios')
_COLNAMES = {'black': (0, 0, 0), 'white': (255, 255, 255), 'red': (255, 0, 0)}
_COLCACHE = {}


def parse_col(c):
    r = _COLCACHE.get(c)
    if r is None:
        try:
            s = c.lstrip('#')
            if c in _COLNAMES:
                r = _COLNAMES[c]
            else:
                if len(s) == 3:
                    s = ''.join(ch * 2 for ch in s)
                r = (int(s[0:2], 16), int(s[2:4], 16), int(s[4:6], 16))
        except Exception:
            r = (255, 0, 255)
        _COLCACHE[c] = r
    return r


class TexImg:
    """A region of an atlas page.  zoom = on-screen pixels per source pixel."""
    __slots__ = ('page', 'u0', 'v0', 'u1', 'v1', 'w', 'h', 'zoom')

    def __init__(self, page, u0, v0, u1, v1, w, h, zoom):
        self.page, self.u0, self.v0, self.u1, self.v1 = page, u0, v0, u1, v1
        self.w, self.h, self.zoom = w, h, zoom


class GlyphRun:
    """A string of 3x5 pixel-font glyphs, expanded to quads when drawn."""
    __slots__ = ('s', 'col', 'zoom')

    def __init__(self, s, col, zoom):
        self.s, self.col, self.zoom = s, col, zoom


class Atlas:
    SZ = 1024
    EPS = 0.02

    def __init__(self):
        self.pages = []
        self.px = self.py = self.rh = 0
        self.sw = {}
        self.glyphs = {}
        self._new()

    def _new(self):
        t = Texture.create(size=(self.SZ, self.SZ), colorfmt='rgba')
        t.mag_filter = 'nearest'
        t.min_filter = 'nearest'
        t.blit_buffer(bytes(self.SZ * self.SZ * 4), colorfmt='rgba', bufferfmt='ubyte')
        self.pages.append(t)
        self.px = self.py = 1
        self.rh = 0

    def alloc(self, w, h):
        if self.px + w + 1 > self.SZ:
            self.px = 1
            self.py += self.rh + 1
            self.rh = 0
        if self.py + h + 1 > self.SZ:
            self._new()
        x, y = self.px, self.py
        self.px += w + 1
        self.rh = max(self.rh, h)
        return len(self.pages) - 1, x, y

    def _blit(self, page, x, y, w, h, buf):
        self.pages[page].blit_buffer(bytes(buf), pos=(x, y), size=(w, h),
                                     colorfmt='rgba', bufferfmt='ubyte')

    def add_grid(self, grid, zoom):
        h = len(grid)
        w = len(grid[0])
        buf = bytearray(w * h * 4)
        for y, row in enumerate(grid):
            for x, col in enumerate(row):
                if col is not None:
                    r, g, b = parse_col(col)
                    i = (y * w + x) * 4
                    buf[i] = r
                    buf[i + 1] = g
                    buf[i + 2] = b
                    buf[i + 3] = 255
        page, x, y = self.alloc(w, h)
        self._blit(page, x, y, w, h, buf)
        S, e = float(self.SZ), self.EPS
        return TexImg(page, (x + e) / S, (y + e) / S, (x + w - e) / S, (y + h - e) / S, w, h, zoom)

    def swatch(self, col):
        s = self.sw.get(col)
        if s is None:
            r, g, b = parse_col(col)
            page, x, y = self.alloc(2, 2)
            self._blit(page, x, y, 2, 2, bytes((r, g, b, 255)) * 4)
            u, v = (x + 1) / float(self.SZ), (y + 1) / float(self.SZ)
            s = TexImg(page, u, v, u, v, 1, 1, 1)
            self.sw[col] = s
        return s

    def glyph(self, ch, col):
        key = (ch, col)
        if key in self.glyphs:
            return self.glyphs[key]
        rows = FONT.get(ch)
        im = None
        if rows:
            g = [[col if rows[y][x] == '1' else None for x in range(3)] for y in range(5)]
            im = self.add_grid(g, 1)
        self.glyphs[key] = im
        return im


_ATLAS = None


def atlas():
    global _ATLAS
    if _ATLAS is None:
        _ATLAS = Atlas()
    return _ATLAS


def _assets_build(self, grid, zoom=None):
    return atlas().add_grid(grid, zoom or self.S)


def _assets_text(self, s, col, size):
    key = (s, col, size)
    im = self.text_cache.get(key)
    if im is None:
        if len(self.text_cache) > 4000:
            self.text_cache = {}
        im = GlyphRun(s, col, self.S * size)
        self.text_cache[key] = im
    return im


Assets.build = _assets_build
Assets.text = _assets_text

_IDX = []
MAXQ = 8000
for _q in range(MAXQ):
    _b = _q * 4
    _IDX.extend((_b, _b + 1, _b + 2, _b, _b + 2, _b + 3))


def build_runs(items, W, H):
    """items -> [(page, vertices, quad_count)], preserving paint order."""
    at = atlas()
    runs = []
    page = -1
    verts = []
    n = 0
    for it in items:
        if it[0] == 0:
            _, x0, y0, x1, y1, col = it
            if x1 <= x0 or y1 <= y0 or x1 < 0 or y1 < 0 or x0 > W or y0 > H:
                continue
            s = at.swatch(col)
            quads = ((s.page, x0, y0, x1, y1, s.u0, s.v0, s.u1, s.v1),)
        else:
            im = it[3]
            if im is None:
                continue
            x, y = it[1], it[2]
            if isinstance(im, GlyphRun):
                z = im.zoom
                quads = []
                for i, ch in enumerate(im.s):
                    if ch == ' ':
                        continue
                    gi = at.glyph(ch, im.col)
                    if gi is None:
                        continue
                    gx = x + i * 4 * z
                    quads.append((gi.page, gx, y, gx + 3 * z, y + 5 * z, gi.u0, gi.v0, gi.u1, gi.v1))
            else:
                x1, y1 = x + im.w * im.zoom, y + im.h * im.zoom
                if x1 < 0 or y1 < 0 or x > W or y > H:
                    continue
                quads = ((im.page, x, y, x1, y1, im.u0, im.v0, im.u1, im.v1),)
        for (pg, x0, y0, x1, y1, u0, v0, u1, v1) in quads:
            if pg != page or n >= MAXQ:
                if n:
                    runs.append((page, verts, n))
                page, verts, n = pg, [], 0
            yt, yb = H - y0, H - y1
            verts += (x0, yb, u0, v1, x1, yb, u1, v1, x1, yt, u1, v0, x0, yt, u0, v0)
            n += 1
    if n:
        runs.append((page, verts, n))
    return runs


class DrawCanvas:
    """Stand-in for tk.Canvas: records rectangles/images, the KView paints them."""

    def __init__(self, root=None, **kw):
        self.items = []
        self.view = getattr(root, 'view', None)

    def pack(self, *a, **k):
        pass

    def bind(self, *a, **k):
        pass

    def config(self, **k):
        if 'cursor' in k and not TT_MOBILE and kplatform in ('win', 'linux', 'macosx'):
            try:
                Window.show_cursor = (k['cursor'] != 'none')
            except Exception:
                pass

    def delete(self, *a):
        self.items = []

    def create_rectangle(self, x0, y0, x1, y1, fill='#000000', outline='', **k):
        self.items.append((0, x0, y0, x1, y1, fill))

    def create_image(self, x, y, image=None, anchor='nw', **k):
        self.items.append((1, x, y, image))

    def flush(self):
        items, self.items = self.items, []
        if self.view is not None:
            self.view.present(items)


class KRoot:
    """Stand-in for tk.Tk (just enough for Game.__init__ and the main loop)."""

    def __init__(self, view):
        self.view = view

    def update(self):
        pass

    def winfo_width(self):
        return int(self.view.width)

    def winfo_height(self):
        return int(self.view.height)

    def winfo_screenwidth(self):
        return int(Window.width)

    def winfo_screenheight(self):
        return int(Window.height)

    def after(self, ms, fn):
        Clock.schedule_once(lambda dt: fn(), 0)

    def bind(self, *a, **k):
        pass

    def protocol(self, *a, **k):
        pass

    def focus_force(self):
        pass

    def attributes(self, *a, **k):
        return False

    def destroy(self):
        app = App.get_running_app()
        if app:
            app.stop()


def _toggle_fullscreen(self):
    if not IS_MOBILE:
        try:
            Window.fullscreen = False if Window.fullscreen else 'auto'
        except Exception:
            pass


Game.toggle_fullscreen = _toggle_fullscreen


# ---- keyboard mapping ---------------------------------------------------------
KEYMAP = {273: 'up', 274: 'down', 275: 'right', 276: 'left', 13: 'return', 271: 'kp_enter',
          27: 'escape', 8: 'backspace', 32: 'space', 9: 'tab', 127: 'delete', 304: 'shift_l',
          303: 'shift_r', 306: 'control_l', 305: 'control_r', 308: 'alt_l', 307: 'alt_r'}
for _i in range(12):
    KEYMAP[282 + _i] = 'f%d' % (_i + 1)
PUNCT = {'/': 'slash', '[': 'bracketleft', ']': 'bracketright', ',': 'comma', '.': 'period',
         '-': 'minus', '=': 'equal', ';': 'semicolon', "'": 'apostrophe', '\\': 'backslash'}


def keysym_of(key):
    if key in KEYMAP:
        return KEYMAP[key]
    if 32 < key < 127:
        ch = chr(key).lower()
        return PUNCT.get(ch, ch)
    return None


# ---- text hooks: remember what was drawn (for tap-to-select) and, on mobile, swap key hints ----
MOBILE_TEXT = {
    'A D MOVE   SPACE JUMP': 'D-PAD MOVE   JUMP BUTTON JUMP',
    'A D / ARROWS': 'D-PAD', 'SPACE / Z / K': 'JUMP BUTTON', 'KEY AWAY FROM FLOOR': 'D-PAD AWAY FROM FLOOR',
    'R': 'R BUTTON', 'ESC / P': 'II BUTTON', 'PAUSE   M MUTE': 'PAUSE',
    'SOUL LANTERN (X)': 'SOUL LANTERN (X BTN)', 'SPARK CLASP (SHIFT)': 'SPARK CLASP (DASH BTN)',
    'DASH WITH SHIFT': 'TAP THE DASH BUTTON',
    'PRESS ENTER': 'TAP TO CONTINUE',
    'E: TALK': '', 'E: ENTER': '', 'E: USE LIFT': '',
}


def mobile_text(s):
    if s in MOBILE_TEXT:
        return MOBILE_TEXT[s]
    if s.startswith('PRESS N TO MAKE'):
        return 'TAP NEW TO MAKE ONE'
    if s.startswith('OR I TO IMPORT'):
        return 'OR TAP IMPORT'
    if s.startswith(('UP DOWN', 'LEFT RIGHT', 'ESC:')):
        return ''
    if s.startswith(('ENTER ', 'ENTER:')) and ('ESC' in s or ':' in s):
        return ''
    return s


_orig_text = Game.text


def _hooked_text(self, s, x, y, col=C_TEXT, size=1, align='l', shadow=True):
    st = str(s).upper()
    if TT_MOBILE:
        st = mobile_text(st)
    if not st:
        return 0
    w = _orig_text(self, st, x, y, col, size, align, shadow)
    x0 = x - w / 2.0 if align == 'c' else (x - w if align == 'r' else x)
    self.__dict__.setdefault('trecs', []).append((st, x0, y, w, size))
    return w


Game.text = _hooked_text
_orig_render = GameV3.render


def _hooked_render(self):
    self.trecs = []
    _orig_render(self)


GameV3.render = _hooked_render


def row_keys(g, vx, vy):
    """A tap at (vx, vy) in game units -> list of key presses that select + activate that list row."""
    recs = getattr(g, 'trecs', [])
    marks = [r for r in recs if r[0] == '>']
    if not marks:
        return None
    best = None
    for m in marks:
        sib = [r for r in recs if r[0] != '>' and abs(r[2] - m[2]) < 1.6 and 0 < r[1] - m[1] < 24]
        if not sib:
            continue
        s0 = min(sib, key=lambda r: r[1])
        col = sorted([r for r in recs if r[0] != '>' and abs(r[1] - s0[1]) < 0.6 and r[4] == s0[4]],
                     key=lambda r: r[2])
        if len(col) < 1:
            continue
        near = min(col, key=lambda r: abs(r[2] + 2.5 * r[4] - vy))
        if abs(near[2] + 2.5 * near[4] - vy) > 5.5 * near[4]:
            continue
        if not (s0[1] - 30 <= vx <= s0[1] + 270):
            continue
        sel = min(col, key=lambda r: abs(r[2] - m[2]))
        delta = col.index(near) - col.index(sel)
        best = (near, delta, s0)
        break
    if best is None:
        return None
    near, delta, s0 = best
    delta = max(-40, min(40, delta))
    keys = ['down'] * delta if delta > 0 else ['up'] * (-delta)
    rel = (vx - near[1]) / max(1.0, near[3])
    if '<' in near[0] and near[0].rstrip().endswith('>'):
        keys.append('right' if rel > 0.8 else ('left' if rel > 0.55 else 'return'))
    else:
        keys.append('return')
    return keys


CONT_STATES = ('howto', 'ending', 'gameover', 'intro', 'clear', 'credits')
MOUSE_FULL = ('editor', 'music')


def modal_active(g):
    st = g.state
    if st == 'editor' and g.editor is not None:
        return bool(getattr(g.editor, 'modal', None) or getattr(g.editor, 'edit', None))
    if st == 'music' and g.mm is not None:
        return bool(getattr(g.mm, 'modal', None) or getattr(g.mm, 'edit', None))
    return False


# ---- on-screen controls (mobile build) ---------------------------------------------------------
class Btn:
    __slots__ = ('id', 'label', 'icon', 'keys', 'kind', 'x', 'y', 'w', 'h')

    def __init__(self, id, label, keys, x, y, w, h, kind='hold', icon=None):
        self.id, self.label, self.keys, self.kind = id, label, keys, kind
        self.x, self.y, self.w, self.h, self.icon = int(x), int(y), int(w), int(h), icon

    def hit(self, px, py):
        return self.x <= px < self.x + self.w and self.y <= py < self.y + self.h


class Pad:
    def __init__(self, view):
        self.view = view
        self.btns = []
        self.sig = None
        self.active = set()
        self.mmode = 'pen'
        self._arrows = {}

    @property
    def g(self):
        return self.view.g

    def context(self, g):
        st = g.state
        script = st == 'play' and getattr(g, 'script', None) is not None
        near = getattr(g, 'near', None) if (st == 'play' and g.mode == 'story') else None
        return (int(self.view.width), int(self.view.height), st, g.mode if st == 'play' else '',
                g.is_typing(), self.mmode, script, near['t'] if near else '', modal_active(g))

    def layout(self, g, ctx):
        W, H, st, mode, typing, mm, script, near, modal = ctx
        bs = int(min(H * 0.17, W * 0.1))
        m = int(bs * 0.25)
        sb = int(bs * 0.7)
        L = []
        rx, ry = W - m, H - m
        ab = int(bs * 1.45)

        def arrows(size):
            cx, cy = m + int(size * 1.55), H - m - int(size * 1.55)
            L.append(Btn('dL', '', ('left',), cx - int(size * 1.5), cy - size // 2, size, size, icon=LEFT))
            L.append(Btn('dR', '', ('right',), cx + size // 2, cy - size // 2, size, size, icon=RIGHT))
            L.append(Btn('dU', '', ('up',), cx - size // 2, cy - int(size * 1.5), size, size, icon=UP))
            L.append(Btn('dD', '', ('down',), cx - size // 2, cy + size // 2, size, size, icon=DOWN))

        def column(items, size):
            y, x = ry - size, rx - size
            for (id_, lab, keys) in items:
                if y < m:
                    y, x = ry - size, x - size - m
                L.append(Btn(id_, lab, keys, x, y, size, size))
                y -= size + m

        if typing:
            L.append(Btn('A', 'DONE', ('return',), W - m - ab, m, ab, sb))
            L.append(Btn('B', 'CANCEL', ('escape',), W - 2 * m - ab - int(ab * 1.2), m, int(ab * 1.2), sb))
            self.btns = L
            return
        if script:
            self.btns = L
            return
        if st == 'play':
            arrows(bs)
            L.append(Btn('A', 'JUMP', ('space',), rx - ab, ry - ab, ab, ab))
            if mode == 'story':
                L.append(Btn('B', 'X', ('x',), rx - ab - m - bs, ry - bs, bs, bs))
                L.append(Btn('D', 'DASH', ('shift_l',), rx - ab - m - bs, ry - 2 * bs - m, bs, bs))
                if near:
                    lab = {'npc': 'TALK', 'warp': 'ENTER', 'lift': 'LIFT'}.get(near, 'E')
                    L.append(Btn('C', lab, ('e',), rx - int(bs * 1.3), ry - ab - m - bs, int(bs * 1.3), bs))
            x = W - m - sb
            L.append(Btn('pause', 'II', ('escape',), x, m, sb, sb))
            L.append(Btn('resp', 'R', ('r',), x - sb - m, m, sb, sb))
        elif st in MOUSE_FULL and not modal:
            y0, step = int(H * 0.16), sb + m // 2
            tools = [('mPEN', 'PEN', ('pen',), 'radio'), ('mERS', 'ERS', ('erase',), 'radio'),
                     ('mPAN', 'PAN', ('pan',), 'radio')]
            if st == 'editor':
                tools += [('kUND', 'UND', ('control_l', 'z'), 'hold'), ('kRED', 'RED', ('control_l', 'y'), 'hold'),
                          ('kSAV', 'SAVE', ('control_l', 's'), 'hold'), ('kTST', 'TEST', ('f5',), 'hold'),
                          ('kGRD', 'GRID', ('g',), 'hold'), ('kQ', 'PREV', ('q',), 'hold'),
                          ('kE', 'NEXT', ('e',), 'hold'), ('kPR', 'PROP', ('f2',), 'hold'),
                          ('kESC', 'EXIT', ('escape',), 'hold')]
            else:
                tools += [('kSP', 'PLAY', ('space',), 'hold'), ('kEN', 'ALL', ('return',), 'hold'),
                          ('kBL', '[', ('bracketleft',), 'hold'), ('kBR', ']', ('bracketright',), 'hold'),
                          ('kSV', 'SAVE', ('control_l', 's'), 'hold'), ('kESC', 'EXIT', ('escape',), 'hold')]
            col = row = 0
            for (id_, lab, keys, kind) in tools:
                L.append(Btn(id_, lab, keys, m + col * (sb + m // 2), y0 + row * step, sb, sb, kind=kind))
                row += 1
                if y0 + (row + 1) * step > H - m:
                    row, col = 0, col + 1
        elif st != 'title':
            L.append(Btn('back', 'BACK', ('escape',), m, m, int(bs * 1.3), sb))
            if modal:
                arrows(int(bs * 0.8))
                column([('A', 'OK', ('return',)), ('E1', 'DEL', ('delete',)), ('E2', 'REMIX', ('c',))], bs)
            elif st == 'custom':
                column([('E1', 'EDIT', ('e',)), ('E2', 'NEW', ('n',)), ('E3', 'IMPORT', ('i',)),
                        ('E4', 'DELETE', ('delete',))], bs)
            elif st == 'online_browser':
                arrows(int(bs * 0.8))
                column([('E1', 'FIND', ('f',)), ('E2', 'CLEAR', ('x',)), ('E3', 'RETRY', ('r',)),
                        ('E4', 'LOGIN', ('l',)), ('E5', 'PUBLISH', ('p',)), ('E6', 'WEB', ('o',))],
                       int(bs * 0.8))
            elif st in ('journal', 'travel', 'shop', 'story_menu', 'select', 'options', 'pause'):
                arrows(int(bs * 0.8))
        self.btns = L

    def refresh_layout(self, g):
        ctx = self.context(g)
        if ctx != self.sig:
            self.sig = ctx
            self.layout(g, ctx)

    def hit(self, px, py):
        for b in reversed(self.btns):
            if b.hit(px, py):
                return b
        return None

    @staticmethod
    def _ev(k, ch=''):
        return SimpleNamespace(keysym=k, char=ch)

    def press(self, b):
        if b.kind == 'radio':
            self.mmode = b.keys[0]
            self.sig = None
        else:
            for k in b.keys:
                self.g.on_down(self._ev(k))

    def release(self, b):
        if b.kind == 'hold':
            for k in reversed(b.keys):
                self.g.on_up(self._ev(k))

    def sync(self, points):
        now = set()
        for (x, y) in points:
            b = self.hit(x, y)
            if b is not None:
                now.add(b.id)
        byid = {b.id: b for b in self.btns}
        for i in list(self.active - now):
            self.active.discard(i)
            if i in byid:
                self.release(byid[i])
        for i in now - self.active:
            self.active.add(i)
            if i in byid:
                self.press(byid[i])

    def release_all(self):
        byid = {b.id: b for b in self.btns}
        for i in list(self.active):
            if i in byid:
                self.release(byid[i])
        self.active = set()

    def draw_items(self, g):
        items = []
        for b in self.btns:
            on = b.id in self.active or (b.kind == 'radio' and b.keys[0] == self.mmode)
            items.append((0, b.x - 2, b.y - 2, b.x + b.w + 2, b.y + b.h + 2, '#8f86d6'))
            items.append((0, b.x, b.y, b.x + b.w, b.y + b.h, '#5a4fb0' if on else '#1c1738'))
            if b.icon is not None:
                z = max(1, int(b.w * 0.5 / 5))
                k = (b.icon, z)
                im = self._arrows.get(k)
                if im is None:
                    im = self._arrows[k] = atlas().add_grid(g_arrow5(b.icon, '#ffffff'), z)
                items.append((1, b.x + (b.w - 5 * z) / 2.0, b.y + (b.h - 5 * z) / 2.0, im))
            elif b.label:
                n = len(b.label)
                z = max(1, min(int(b.w * 0.84 / (4 * n - 1)), int(b.h * 0.4 / 5)))
                tw = (4 * n - 1) * z
                items.append((1, b.x + (b.w - tw) / 2.0, b.y + (b.h - 5 * z) / 2.0,
                              GlyphRun(b.label, '#ffffff', z)))
        return items


class KView(Widget):
    SENT = 'x' * 16

    def __init__(self, **kw):
        super().__init__(**kw)
        self.g = None
        self.pad = Pad(self) if TT_MOBILE else None
        self.tp = {}
        self.mouse_uid = None
        self.mouse_btn = 1
        self.keyq = []
        self.qheld = None
        self.qwait = 0
        self.ti = None
        self.ti_reset = False
        self.ti_seen = False
        self.was_typing = False
        self.bind(size=self._on_size)
        Window.bind(on_key_down=self._key_down, on_key_up=self._key_up, mouse_pos=self._mouse_pos,
                    on_textinput=self._textinput)
        if TT_MOBILE:
            from kivy.uix.textinput import TextInput
            self.ti = TextInput(multiline=False, size_hint=(None, None), size=(12, 12), opacity=0,
                                text=self.SENT, write_tab=False)
            try:
                self.ti.keyboard_suggestions = False
            except Exception:
                pass
            self.ti.bind(text=self._ti_text, on_text_validate=self._ti_enter)
            self.add_widget(self.ti)
            try:
                Window.softinput_mode = 'below_target'
            except Exception:
                pass

    # -- lifecycle
    def start(self):
        self.size = Window.size
        self.canvas.before.clear()
        self.g = GameV3(KRoot(self), '--windowed' in sys.argv, '--mute' in sys.argv)

    def _on_size(self, *a):
        if self.ti is not None:
            self.ti.pos = (0, self.height - 12)
        g = self.g
        if g is not None and self.width > 200 and self.height > 150:
            g.apply_size(int(self.width), int(self.height))

    # -- native keyboard (mobile): a hidden TextInput feeds the game's text boxes
    def _ti_text(self, inst, val):
        g = self.g
        if self.ti_reset or g is None:
            return
        S = self.SENT
        if val != S:
            if val.startswith(S):
                for ch in val[len(S):]:
                    if ch.isprintable():
                        g.chars.append(ch)
            elif S.startswith(val):
                for _ in range(len(S) - len(val)):
                    g.events.append('backspace')
            else:
                for ch in val:
                    if ch.isprintable():
                        g.chars.append(ch)
            self._ti_clear()

    def _ti_clear(self):
        self.ti_reset = True
        self.ti.text = self.SENT
        try:
            self.ti.cursor = (len(self.SENT), 0)
        except Exception:
            pass
        self.ti_reset = False

    def _ti_enter(self, *a):
        if self.g is not None:
            self.g.events.append('return')
            Clock.schedule_once(lambda dt: self._refocus(), 0.05)

    def _refocus(self):
        if self.ti is not None and self.g is not None and self.g.is_typing():
            self.ti.focus = True

    def _sync_typing(self, g):
        if self.ti is None:
            return
        typing = g.is_typing()
        if typing and not self.was_typing:
            pe = getattr(g, 'portal_edit', None)
            self.ti.password = bool(pe is not None and pe.get('kind') == 'pass')
            self._ti_clear()
            self.ti.focus = True
        elif self.was_typing and not typing:
            self.ti.focus = False
        self.was_typing = typing

    # -- drawing
    def _pump_keys(self, g):
        if self.qwait > 0:
            self.qwait -= 1
            return
        if self.qheld is not None:
            g.on_up(SimpleNamespace(keysym=self.qheld, char=''))
            g.rel.pop(self.qheld, None)
            g.held.discard(self.qheld)
            self.qheld = None
            self.qwait = 0
        elif self.keyq:
            self.qheld = self.keyq.pop(0)
            g.on_down(SimpleNamespace(keysym=self.qheld, char=''))
            self.qwait = 0

    def present(self, items):
        g = self.g
        W, H = self.width, self.height
        overlay = []
        if g is not None:
            self._pump_keys(g)
            if TT_MOBILE:
                self._sync_typing(g)
                self.pad.refresh_layout(g)
                overlay = self.pad.draw_items(g)
        runs = build_runs(items, W, H)
        oruns = build_runs(overlay, W, H)
        at = atlas()
        r, gg, b = parse_col(C_BG)
        cv = self.canvas.before
        cv.clear()
        with cv:
            Color(r / 255.0, gg / 255.0, b / 255.0, 1)
            Rectangle(pos=(0, 0), size=(W, H))
            Color(1, 1, 1, 1)
            for (pg, verts, n) in runs:
                Mesh(vertices=verts, indices=_IDX[:6 * n], mode='triangles', texture=at.pages[pg])
            Color(1, 1, 1, 0.6)
            for (pg, verts, n) in oruns:
                Mesh(vertices=verts, indices=_IDX[:6 * n], mode='triangles', texture=at.pages[pg])

    # -- physical keyboard
    def _key_down(self, win, key, scancode=None, codepoint=None, modifier=None, *a):
        g = self.g
        if g is None:
            return False
        k = keysym_of(key)
        if k is None:
            return False
        typing = g.is_typing()
        if TT_MOBILE and typing and k != 'escape':
            return False                       # the hidden TextInput handles it
        ch = ''
        if typing and not self.ti_seen and isinstance(codepoint, str):
            ch = codepoint
        g.on_down(SimpleNamespace(keysym=k, char=ch))
        return True

    def _key_up(self, win, key, *a):
        g = self.g
        if g is None:
            return False
        k = keysym_of(key)
        if TT_MOBILE and g.is_typing() and k != 'escape':
            return False
        if k is not None:
            g.on_up(SimpleNamespace(keysym=k, char=''))
        return True

    def _textinput(self, win, text):
        g = self.g
        if g is None or TT_MOBILE:
            return False
        if not self.ti_seen:
            self.ti_seen = True
            return False                       # first char was already taken from the key event
        if g.is_typing():
            for ch in text:
                if ch.isprintable():
                    g.chars.append(ch)
        return False

    def _mouse_pos(self, win, pos):
        g = self.g
        if g is not None and self.mouse_uid is None and kplatform not in ('android', 'ios'):
            g.m_move(SimpleNamespace(x=pos[0], y=self.height - pos[1]))

    # -- touch / mouse
    def _free_points(self):
        return [p for uid, p in self.tp.items() if uid != self.mouse_uid]

    def on_touch_down(self, t):
        g = self.g
        if g is None:
            return False
        btn = getattr(t, 'button', 'left')
        if btn in ('scrollup', 'scrolldown'):
            g.mev.append(('wheel', -1 if btn == 'scrollup' else 1, 0, 0))
            return True
        dev = getattr(t, 'device', '')
        x, y = t.x, self.height - t.y
        self.tp[t.uid] = (x, y)
        if TT_MOBILE and self.pad.hit(x, y) is not None:
            self.pad.sync(self._free_points())
            return True
        typing = g.is_typing()
        if typing:
            if self.ti is not None:
                self.ti.focus = True
            return True
        st = g.state
        if st in MOUSE_FULL and not modal_active(g):
            if self.mouse_uid is None:
                if TT_MOBILE and dev != 'mouse':
                    b = {'pen': 1, 'pan': 2, 'erase': 3}[self.pad.mmode]
                else:
                    b = {'left': 1, 'middle': 2, 'right': 3}.get(btn, 1)
                self.mouse_uid, self.mouse_btn = t.uid, b
                g.m_down(b, SimpleNamespace(x=x, y=y))
            return True
        if btn in ('left', None) or dev != 'mouse':
            S = float(g.S)
            keys = row_keys(g, x / S, y / S)
            if keys is None and (st in CONT_STATES or (st == 'play' and getattr(g, 'script', None) is not None)):
                keys = ['return']
            if keys:
                self.keyq.extend(keys)
        if TT_MOBILE:
            self.pad.sync(self._free_points())
        return True

    def on_touch_move(self, t):
        g = self.g
        if g is None or t.uid not in self.tp:
            return False
        self.tp[t.uid] = (t.x, self.height - t.y)
        if t.uid == self.mouse_uid:
            g.m_move(SimpleNamespace(x=t.x, y=self.height - t.y))
        elif TT_MOBILE:
            self.pad.sync(self._free_points())
        return True

    def on_touch_up(self, t):
        g = self.g
        if g is None or t.uid not in self.tp:
            return False
        x, y = self.tp.pop(t.uid)
        if t.uid == self.mouse_uid:
            self.mouse_uid = None
            g.m_up(self.mouse_btn, SimpleNamespace(x=x, y=y))
        elif TT_MOBILE:
            self.pad.sync(self._free_points())
        return True


# ---- audio: Kivy SoundLoader instead of afplay / paplay / winmm ---------------------------
def _ka_init(self, mute=False):
    self.ok = False
    self.muted = mute
    self.mvol = 6
    self.svol = 8
    self.dir = CACHE_DIR
    self.win = None
    self.cmdline = None
    self.ready_sfx = set()
    self.loaded = set()
    self.last_play = {}
    self.sfx_n = 0
    self.want = None
    self.cur = None
    self.music_ready = {}
    self.music_proc = None
    self.tickn = 0
    self.gen_lock = threading.Lock()
    self.snds = {}
    self.msnd = None
    try:
        try:
            os.makedirs(self.dir, exist_ok=True)
            open(os.path.join(self.dir, '.w'), 'w').close()
        except Exception:
            self.dir = tempfile.mkdtemp(prefix='tt_audio_')
        from kivy.core.audio import SoundLoader
        self._SL = SoundLoader
        self.ok = True
    except Exception:
        self.ok = False
    if self.ok:
        threading.Thread(target=self._render_sfx, daemon=True).start()


def _ka_play(self, name):
    if not self.ok or self.muted or self.svol <= 0 or name not in self.ready_sfx:
        return
    now = time.perf_counter()
    if now - self.last_play.get(name, 0) < 0.05:
        return
    self.last_play[name] = now
    try:
        pool = self.snds.setdefault(name, [])
        if len(pool) < 2:
            s = self._SL.load(os.path.join(self.dir, 'sfx_%s.wav' % name))
            if s is None:
                return
            pool.append(s)
        self.sfx_n += 1
        s = pool[self.sfx_n % len(pool)]
        s.volume = self.gain(self.svol)
        s.stop()
        s.play()
    except Exception:
        pass


def _ka_stop_music(self):
    try:
        if self.msnd is not None:
            self.msnd.stop()
            self.msnd.unload()
    except Exception:
        pass
    self.msnd = None
    self.cur = None


def _ka_set_volumes(self):
    try:
        if self.msnd is not None:
            self.msnd.volume = 0.0 if self.muted else self.gain(self.mvol) * 0.7
    except Exception:
        pass


def _ka_tick(self):
    if not self.ok:
        return
    self.tickn += 1
    try:
        if self.want and self.cur != self.want and self.want in self.music_ready:
            s = self._SL.load(self.music_ready[self.want])
            self.cur = self.want
            if s is not None:
                s.loop = True
                s.volume = 0.0 if self.muted else self.gain(self.mvol) * 0.7
                s.play()
                self.msnd = s
    except Exception:
        pass


def _ka_shutdown(self):
    self.stop_music()


Audio.__init__ = _ka_init
Audio.play = _ka_play
Audio.stop_music = _ka_stop_music
Audio.set_volumes = _ka_set_volumes
Audio.tick = _ka_tick
Audio.shutdown = _ka_shutdown


# ---- files, links, dialogs ----------------------------------------------------------------
def storage_dirs():
    out = []
    if kplatform == 'android':
        out += ['/storage/emulated/0/Download', '/storage/emulated/0/Documents']
    else:
        out.append(os.path.join(os.path.expanduser('~'), 'Downloads'))
    out.append(LEVELS_DIR)
    return out


def export_target(fname):
    """Where an exported file goes: the shared Downloads folder if writable, else levels/."""
    for d in storage_dirs():
        try:
            if os.path.isdir(d):
                p = os.path.join(d, fname)
                open(p, 'a').close()
                return p
        except Exception:
            continue
    return os.path.join(LEVELS_DIR, fname)


def open_url(url):
    try:
        if kplatform == 'android':
            from jnius import autoclass
            Intent = autoclass('android.content.Intent')
            Uri = autoclass('android.net.Uri')
            PA = autoclass('org.kivy.android.PythonActivity')
            it = Intent(Intent.ACTION_VIEW, Uri.parse(url))
            PA.mActivity.startActivity(it)
        else:
            import webbrowser
            webbrowser.open(url)
    except Exception:
        pass


def _pick_file(self, exts, cb, title='OPEN FILE'):
    from kivy.uix.popup import Popup
    from kivy.uix.boxlayout import BoxLayout
    from kivy.uix.button import Button
    from kivy.uix.filechooser import FileChooserListView
    start = next((d for d in storage_dirs() if os.path.isdir(d)), _HERE)
    fc = FileChooserListView(path=start, filters=['*' + e for e in exts] if exts else [])
    box = BoxLayout(orientation='vertical')
    box.add_widget(fc)
    row = BoxLayout(size_hint_y=None, height=56)
    ok, cancel = Button(text='Import'), Button(text='Cancel')
    row.add_widget(ok)
    row.add_widget(cancel)
    box.add_widget(row)
    pop = Popup(title=title, content=box, size_hint=(0.9, 0.9), auto_dismiss=False)

    def _ok(*a):
        sel = fc.selection
        pop.dismiss()
        if sel:
            cb(sel[0])

    ok.bind(on_release=_ok)
    cancel.bind(on_release=lambda *a: pop.dismiss())
    pop.open()


def _import_custom_level(self, p):
    try:
        with open(p, 'r', encoding='utf-8-sig') as fh:
            d = text_to_data(fh.read())
        os.makedirs(LEVELS_DIR, exist_ok=True)
        with open(os.path.join(LEVELS_DIR, safe_name(d['name']) + '.tttl'), 'w', encoding='utf-8') as fo:
            fo.write(data_to_text(d))
        self.custom_files = list_files(LEVELS_DIR, '.tttl')
        self.custom_meta = {}
        self.toast = ['MAP IMPORTED: ' + self._pstr(d['name'], 'UNTITLED', 30), 180]
    except Exception:
        self.toast = ['IMPORT FAILED', 150]


def _import_song(self, p):
    try:
        with open(p, 'r', encoding='utf-8-sig') as f:
            s = text_to_song(f.read())
        os.makedirs(MUSIC_DIR, exist_ok=True)
        self.path = os.path.join(MUSIC_DIR, safe_name(s['name']) + '.tttm')
        self.song = s
        self.save()
    except Exception:
        self.say('IMPORT FAILED')


GameV3.pick_file = _pick_file
GameV3._import_custom_level = _import_custom_level
MusicMaker._import_song = _import_song


# ---- the app ----------------------------------------------------------------------------------
class TurningTowerApp(App):
    title = 'The Turning Tower'

    def build(self):
        if not TT_MOBILE:
            try:
                import base64
                ip = os.path.join(_HERE, 'icon.png')
                with open(ip, 'wb') as f:
                    f.write(base64.b64decode(''.join(ICON_B64)))
                Window.set_icon(ip)
            except Exception:
                pass
        if kplatform == 'android':
            try:
                from android.permissions import request_permissions, Permission
                request_permissions([Permission.READ_EXTERNAL_STORAGE, Permission.WRITE_EXTERNAL_STORAGE])
            except Exception:
                pass
        Window.clearcolor = (0.04, 0.03, 0.075, 1)
        self.view = KView()
        return self.view

    def on_start(self):
        Clock.schedule_once(lambda dt: self.view.start(), 0.05)

    def on_pause(self):
        g = self.view.g
        if g is not None:
            g.write_save()
            g.audio.stop_music()
        return True

    def on_resume(self):
        g = self.view.g
        if g is not None:
            g.audio.cur = None
            if self.view.pad is not None:
                self.view.pad.release_all()
            g.held.clear()

    def on_stop(self):
        g = self.view.g
        if g is not None:
            g.running = False
            g.write_save()
            g.audio.shutdown()


def main():
    TurningTowerApp().run()


if __name__ == '__main__':
    main()
