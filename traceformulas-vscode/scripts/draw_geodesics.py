#!/usr/bin/env python3
"""Regenerate Section 1.3's vector diagram (optional authoring dependency: Matplotlib).

The ordinary website/PDF build uses the checked-in SVG/PDF pair and does not
need Matplotlib. Both panels use the same exact circle and fractional map.
"""
from pathlib import Path
import os
os.environ.setdefault('MPLCONFIGDIR', '/tmp/traceformulas-matplotlib')
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'volumes/Volume01/A/chapters/Chapter01/sections/Section03/figures'


def main():
    plt.rcParams.update({'font.family': 'DejaVu Serif', 'font.size': 12,
                         'svg.fonttype': 'path', 'svg.hashsalt': 'traceformulas-geodesics',
                         'pdf.fonttype': 42})
    ink, teal, gray = '#243b39', '#147d79', '#79858b'
    r, radius = 0.0, 2.0
    r1, r2 = r-radius, r+radius
    z, w = -1.2+1.6j, 1.6+1.2j
    h = lambda q: (q-r1)/(r2-q)
    assert abs(abs(z-r)-radius) < 1e-12 and abs(abs(w-r)-radius) < 1e-12
    assert abs(h(z).real) < 1e-12 and abs(h(w).real) < 1e-12
    assert np.allclose([h(z).imag, h(w).imag], [0.5, 3.0])
    fig, (left, right) = plt.subplots(1, 2, figsize=(9.2, 3.9),
                                      gridspec_kw={'width_ratios': [1.4, 1]})
    for ax in (left, right):
        ax.set_aspect('equal'); ax.axis('off')
    t = np.linspace(0, np.pi, 300)
    left.plot(r+radius*np.cos(t), radius*np.sin(t), color=gray, lw=1.6)
    selected = np.linspace(np.angle(w-r), np.angle(z-r), 140)
    left.plot(r+radius*np.cos(selected), radius*np.sin(selected), color=teal, lw=4)
    left.annotate('', xy=(2.65,0), xytext=(-2.65,0),
                  arrowprops={'arrowstyle':'->','color':ink,'lw':1})
    left.plot([z.real,w.real], [z.imag,w.imag], color=gray, lw=1, ls=':')
    midpoint = (z+w)/2
    left.plot([r,1.6*midpoint.real], [0,1.6*midpoint.imag], color=gray, lw=1, ls=':')
    for q,name,offset in [(z,'$z$',(-15,9)), (w,'$w$',(8,9))]:
        left.plot([r,q.real],[0,q.imag], color=gray, lw=1.2, ls='--')
        left.plot(q.real,q.imag,'o',color=teal,ms=6)
        left.annotate(name,(q.real,q.imag),xytext=offset,textcoords='offset points',color=ink)
    left.text(-.80,.72,'$R$',color=gray); left.text(.65,.72,'$R$',color=gray)
    for x,name in [(r1,'$r_1$'),(r,'$r$'),(r2,'$r_2$')]:
        left.plot(x,0,'o',color=ink,ms=4)
        left.text(x,-.18,name,ha='center',va='top',color=ink)
    left.text(0,2.36,'The circle through $z$ and $w$',ha='center',color=ink)
    left.set_xlim(-2.7,2.7);left.set_ylim(-.5,2.7)
    right.annotate('',xy=(0,3.55),xytext=(0,0),
                   arrowprops={'arrowstyle':'->','color':ink,'lw':1})
    right.annotate('',xy=(1.55,0),xytext=(-.7,0),
                   arrowprops={'arrowstyle':'->','color':ink,'lw':1})
    right.plot([0,0],[h(z).imag,h(w).imag],color=teal,lw=4)
    for q,label in [(z,'$h(z)=it_1$'),(w,'$h(w)=it_2$')]:
        right.plot(0,h(q).imag,'o',color=teal,ms=6)
        right.text(.17,h(q).imag,label,va='center',color=ink)
    right.text(-.1,-.18,'$0$',ha='center',va='top',color=ink)
    right.text(0,3.68,r'$\infty$',ha='center',color=ink)
    right.text(.65,4.05,'The vertical image',ha='center',color=ink)
    right.set_xlim(-.75,2.05);right.set_ylim(-.5,4.35)
    fig.text(.59,.50,r'$\longrightarrow$',ha='center',fontsize=25,color=ink)
    fig.text(.59,.40,r'$h(\zeta)=\dfrac{\zeta-r_1}{r_2-\zeta}$',ha='center',fontsize=11,color=ink)
    fig.subplots_adjust(left=.025,right=.99,top=.95,bottom=.06,wspace=.42)
    OUT.mkdir(parents=True,exist_ok=True)
    fig.savefig(OUT/'geodesics.svg',bbox_inches='tight',metadata={'Date':None})
    fig.savefig(OUT/'geodesics.pdf',bbox_inches='tight',metadata={'CreationDate':None,'ModDate':None})
    plt.close(fig)
    print('Generated geodesics.svg and geodesics.pdf from the same coordinates.')


if __name__=='__main__':
    main()
