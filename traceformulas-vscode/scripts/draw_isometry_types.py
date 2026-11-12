#!/usr/bin/env python3
"""Regenerate Section 1.5's paired SVG/PDF diagrams with exact normal-form maps.

Matplotlib is an optional authoring dependency. Ordinary builds use the saved
vector assets and do not need this script or its plotting dependencies.
"""
from pathlib import Path
import os
os.environ.setdefault('MPLCONFIGDIR', '/tmp/traceformulas-matplotlib')
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'volumes/Volume01/A/chapters/Chapter01/sections/Section05/figures'
INK, TEAL, ORANGE, GRAY = '#243b39', '#147d79', '#b45c24', '#899496'


def arrow(ax, points, color=TEAL, index=None):
    index = len(points) // 2 if index is None else index
    p, q = points[index-2], points[index+2]
    ax.annotate('', xy=(q.real, q.imag), xytext=(p.real, p.imag),
                arrowprops={'arrowstyle': '-|>', 'color': color, 'lw': 1.7,
                            'mutation_scale': 14})


def dot(ax, z, color, label=None, offset=(6, 6)):
    ax.plot(z.real, z.imag, 'o', color=color, ms=6, zorder=4)
    if label:
        ax.annotate(label, (z.real, z.imag), xytext=offset,
                    textcoords='offset points', color=color)


def setup_half(ax, xmax, ymax):
    ax.set_aspect('equal')
    ax.axis('off')
    ax.annotate('', xy=(xmax, 0), xytext=(-xmax, 0),
                arrowprops={'arrowstyle': '->', 'color': INK, 'lw': 1})
    ax.text(xmax, -.14, r'$\mathbb{R}$', ha='right', va='top', color=INK)
    ax.text(xmax-.1, ymax-.2, r'$\mathbb{H}$', ha='right', color=INK)
    ax.set_xlim(-xmax-.12, xmax+.12)
    ax.set_ylim(-.35, ymax)


def save(fig, name):
    OUT.mkdir(parents=True, exist_ok=True)
    fig.savefig(OUT / f'{name}.svg', bbox_inches='tight', metadata={'Date': None})
    fig.savefig(OUT / f'{name}.pdf', bbox_inches='tight',
                metadata={'CreationDate': None, 'ModDate': None})
    plt.close(fig)


def elliptic():
    fig, (half, disk) = plt.subplots(1, 2, figsize=(9.2, 4.1))
    inv = lambda z: 1j*(1+z)/(1-z)
    cayley = lambda z: (z-1j)/(z+1j)
    theta = .5
    action = lambda z: (np.cos(theta)*z+np.sin(theta))/(-np.sin(theta)*z+np.cos(theta))
    phi = np.linspace(0, 2*np.pi, 600)
    setup_half(half, 1.85, 3.55)
    disk.set_aspect('equal'); disk.axis('off')
    disk.plot(np.cos(phi), np.sin(phi), color=INK, lw=1.2)
    for rho in (.28, .5):
        circle = rho*np.exp(1j*phi)
        curve = inv(circle)
        assert np.all(curve.imag > 0)
        assert np.allclose(cayley(curve), circle)
        half.plot(curve.real, curve.imag, color=GRAY, lw=1.1)
        disk.plot(circle.real, circle.imag, color=GRAY, lw=1.1)
    segment = .5*np.exp(1j*np.linspace(.2, .2+2*theta, 100))
    transformed = inv(segment)
    assert np.allclose(action(transformed[0]), transformed[-1])
    for ax, curve in [(half, transformed), (disk, segment)]:
        ax.plot(curve.real, curve.imag, color=TEAL, lw=2.5)
        arrow(ax, curve)
    dot(half, 1j, INK, '$i$', (7,-3))
    dot(disk, 0j, INK, '$0$', (-15,-4))
    dot(half, transformed[0], TEAL, '$z$', (7,4))
    dot(half, transformed[-1], ORANGE, r'$k(\theta)\cdot z$', (-73,-5))
    dot(disk, segment[0], TEAL, r'$\zeta$', (6,-8))
    dot(disk, segment[-1], ORANGE, r'$e^{2i\theta}\zeta$', (7,6))
    half.set_title('Elliptic motion in the half-plane', fontsize=12, color=INK, pad=10)
    disk.set_title('Rotation in the disk', fontsize=12, color=INK, pad=10)
    disk.text(.82,-.9,r'$\mathbb{D}$',color=INK)
    disk.set_xlim(-1.12,1.12); disk.set_ylim(-1.13,1.13)
    fig.text(.51,.53,r'$\longrightarrow$',ha='center',fontsize=23,color=INK)
    fig.text(.51,.43,r'$C$',ha='center',fontsize=13,color=INK)
    fig.subplots_adjust(left=.025,right=.985,top=.86,bottom=.06,wspace=.32)
    save(fig, 'elliptic-motion')


def parabolic():
    fig, left = plt.subplots(figsize=(9.2, 2.6))
    setup_half(left, 3.8, 1.85)
    left.set_title(r'Parabolic: $z\mapsto z+t$',fontsize=12,color=INK,pad=10)
    for height in (.55, 1.3):
        left.plot([-3.2,3.2],[height,height],color=GRAY,lw=1.1)
        curve=np.linspace(-1.5,.2,100)+1j*height
        left.plot(curve.real,curve.imag,color=TEAL,lw=2.5)
        arrow(left,curve)
        dot(left,curve[0],TEAL); dot(left,curve[-1],ORANGE)
        left.text(-.65,height+.14,'$t$',ha='center',color=INK)
    left.text(2,1.62,r'fixed point: $\infty$',ha='center',color=INK,fontsize=11)
    fig.subplots_adjust(left=.035,right=.985,top=.82,bottom=.06)
    save(fig,'parabolic-motion')


def hyperbolic_axis():
    fig, (left, right) = plt.subplots(1, 2, figsize=(9.2, 3.9),
                                      gridspec_kw={'width_ratios':[1.35,1]})
    # h(z)=(z+2)/(2-z) straightens the axis with endpoints -2,2.
    # g=h^{-1} a(3) h translates along it by log(3).
    h = lambda z: (z+2)/(2-z)
    hinv = lambda w: (2*w-2)/(w+1)
    scale = 3.0
    distance = np.log(scale)
    heights = np.exp(np.linspace(np.log(.5),np.log(.5)+distance,150))
    vertical = 1j*heights
    segment = hinv(vertical)
    g = lambda z: ((2*scale+2)*z+4*scale-4)/((scale-1)*z+2*scale+2)
    assert np.allclose(h(segment),vertical)
    assert np.allclose(np.abs(segment),2)
    assert np.all(segment.imag>0)
    assert np.allclose(g(segment),hinv(scale*h(segment)))
    assert np.allclose(g(segment[0]),segment[-1])
    assert np.allclose([g(-2),g(2)],[-2,2])
    assert np.allclose(np.log(heights[-1]/heights[0]),distance)
    phi=np.linspace(0,np.pi,300)
    setup_half(left,2.65,2.8)
    left.plot(2*np.cos(phi),2*np.sin(phi),color=GRAY,lw=1.6)
    left.plot(segment.real,segment.imag,color=TEAL,lw=3)
    arrow(left,segment)
    dot(left,segment[0],TEAL,'$z$',(-17,8))
    dot(left,segment[-1],ORANGE,r'$g\cdot z$',(8,8))
    dot(left,-2+0j,INK,'$p_-$',(-9,-20))
    dot(left,2+0j,INK,'$p_+$',(-9,-20))
    left.text(0,.72,'invariant geodesic',ha='center',color=INK,fontsize=11)
    # Right-angle markers at the boundary fixed points.
    for x,sgn in [(-2,1),(2,-1)]:
        left.plot([x,x+sgn*.15,x+sgn*.15],[.15,.15,0],color=GRAY,lw=1)
    left.set_title('Hyperbolic motion along its axis',fontsize=12,color=INK,pad=10)
    setup_half(right,1.5,2.8)
    right.annotate('',xy=(0,2.35),xytext=(0,0),
                   arrowprops={'arrowstyle':'->','color':GRAY,'lw':1.6})
    right.plot(vertical.real,vertical.imag,color=TEAL,lw=3)
    arrow(right,vertical)
    dot(right,vertical[0],TEAL,r'$h(z)=iy$',(9,-3))
    dot(right,vertical[-1],ORANGE,r'$h(g\cdot z)=ie^r y$',(9,-3))
    dot(right,0j,INK,'$0$',(-4,-20))
    right.text(0,2.4,r'$\infty$',ha='center',color=INK)
    right.text(-.15,1.02,r'$r$',ha='right',color=TEAL)
    right.set_title('After conjugation: dilation',fontsize=12,color=INK,pad=10)
    fig.text(.565,.53,r'$\longrightarrow$',ha='center',fontsize=23,color=INK)
    fig.text(.565,.43,r'$h$',ha='center',fontsize=13,color=INK)
    fig.subplots_adjust(left=.025,right=.98,top=.85,bottom=.1,wspace=.55)
    # Preserve the existing asset URL and manuscript figure destination.
    save(fig,'translation-dilation')


def main():
    plt.rcParams.update({'font.family':'DejaVu Serif','font.size':12,
                         'svg.fonttype':'path','svg.hashsalt':'traceformulas-isometry-types',
                         'pdf.fonttype':42})
    elliptic()
    parabolic()
    hyperbolic_axis()
    print('Generated three Section 1.5 SVG/PDF pairs from checked Möbius coordinates.')


if __name__ == '__main__': main()
