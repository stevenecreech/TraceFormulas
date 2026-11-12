"""Reproducible vector figures of the modular domain and actual SL(2,Z) images."""
from pathlib import Path
import math
import os

os.environ.setdefault("MPLCONFIGDIR", "/tmp/traceformulas-matplotlib")
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "volumes/Volume01/A/chapters/Chapter01/sections/Section06/figures"
plt.rcParams.update({"font.family": "DejaVu Serif", "font.size": 12,
                     "svg.fonttype": "path", "svg.hashsalt": "modular-domain",
                     "pdf.fonttype": 42})
BLUE, TEAL, GOLD = "#285e92", "#0c807c", "#f2cd71"
HEIGHT = math.sqrt(3) / 2


def save(fig, name):
    OUT.mkdir(parents=True, exist_ok=True)
    fig.savefig(OUT / f"{name}.svg", bbox_inches="tight", metadata={"Date": None})
    fig.savefig(OUT / f"{name}.pdf", bbox_inches="tight",
                metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)


def axes(ax, xlim, ylim):
    ax.set(xlim=xlim, ylim=ylim, aspect="equal", xlabel=r"$\operatorname{Re} z$",
           ylabel=r"$\operatorname{Im} z$")
    ax.spines[["top", "right"]].set_visible(False)
    ax.spines["bottom"].set_position(("data", 0))
    ax.spines["left"].set_color("#999999")
    ax.tick_params(labelsize=10)


def domain():
    fig, ax = plt.subplots(figsize=(7.2, 5.9))
    x = np.linspace(-.5, .5, 201)
    ax.fill_between(x, np.sqrt(1-x*x), 2.8, color=GOLD, alpha=.55, linewidth=0)
    ax.plot([0, 0], [1, 2.8], "--", color="#888888", linewidth=1.2)
    for side in (-.5, .5):
        ax.plot([side, side], [HEIGHT, 2.70], color=BLUE, linewidth=2)
        ax.annotate("", xy=(side, 2.25), xytext=(side, 1.90),
                    arrowprops={"arrowstyle": "->", "color": BLUE, "lw": 2})
        ax.text(side + (-.16 if side < 0 else .10), 2.05, "$T$", color=BLUE)
        ax.annotate("", xy=(side, 2.76), xytext=(side, 2.53),
                    arrowprops={"arrowstyle": "->", "color": BLUE})
    for lo, hi in ((math.pi/3, math.pi/2), (math.pi/2, 2*math.pi/3)):
        theta = np.linspace(lo, hi, 81)
        ax.plot(np.cos(theta), np.sin(theta), color=TEAL, linewidth=2)
    for sign in (-1, 1):
        p, q = sign * .38 + 1j*math.sqrt(1-.38**2), sign * .16 + 1j*math.sqrt(1-.16**2)
        ax.annotate("", xy=(q.real, q.imag), xytext=(p.real, p.imag),
                    arrowprops={"arrowstyle": "->", "color": TEAL, "lw": 2,
                                "connectionstyle": f"arc3,rad={sign*.07}"})
        ax.text(sign * .29, .71, "$S$", color=TEAL, ha="center")
    for px, py, label, dx, dy in ((-.5, HEIGHT, r"$\rho$", -.15, -.16),
                                 (.5, HEIGHT, r"$\rho+1$", .04, -.16),
                                 (0, 1, "$i$", .06, .06)):
        ax.plot(px, py, "o", color="#25374a", markersize=5)
        ax.text(px+dx, py+dy, label)
    ax.text(-.30, 1.75, r"$\mathcal{F}$", fontsize=23)
    ax.text(.73, 2.49, "extends to\nthe cusp", fontsize=10, color="#555555")
    ax.text(-1.18, 1.34, "paired arcs", color=TEAL, fontsize=10)
    ax.annotate("", xy=(-.34, .95), xytext=(-.76, 1.30),
                arrowprops={"arrowstyle": "->", "color": TEAL, "lw": .8})
    axes(ax, (-1.28, 1.28), (-.04, 2.8))
    ax.set_xticks([-1, -.5, 0, .5, 1])
    ax.set_yticks([1, 2])
    save(fig, "fundamental-domain")


def image(g, z):
    a, b, c, d = g
    assert a*d-b*c == 1
    return (a*z+b)/(c*z+d)


def tiling():
    # The artificial cap is at height 10^5; its images lie below the crop
    # for c != 0. Only the three genuine boundary pieces are stroked.
    y = np.geomspace(HEIGHT, 1e5, 350)
    arc = np.exp(1j*np.linspace(2*math.pi/3, math.pi/3, 120))
    boundary = np.concatenate([-.5+1j*y[::-1], arc, .5+1j*y])
    pieces = [-.5+1j*y, arc, .5+1j*y]
    matrices = [(1, k, 0, 1) for k in range(-3, 4)]
    for c in range(1, 7):
        for d in range(-9, 10):
            if math.gcd(c, d) != 1:
                continue
            a = 0 if c == 1 else pow(d, -1, c)
            b = (a*d-1)//c
            for k in range(-3, 3):
                matrices.append((a+k*c, b+k*d, c, d))
    assert len(matrices) == len(set(matrices))
    fig, ax = plt.subplots(figsize=(9, 5.4))
    for g in matrices:
        z = image(g, boundary)
        if z.real.max() < -2.35 or z.real.min() > 2.35 or z.imag.max() < .075:
            continue
        color = GOLD if g == (1, 0, 0, 1) else "#deebf4"
        ax.fill(z.real, z.imag, color=color, linewidth=0, zorder=1)
        for piece in pieces:
            w = image(g, piece)
            ax.plot(w.real, w.imag, color="#57738c", linewidth=.65, zorder=2)
    for x, label in ((-1, r"$T^{-1}\mathcal{F}$"), (0, r"$\mathcal{F}$"),
                     (1, r"$T\mathcal{F}$")):
        ax.text(x, 1.80, label, ha="center", fontsize=17, zorder=3)
    ax.text(0, .43, r"$S\mathcal{F}$", ha="center", fontsize=13, zorder=3)
    axes(ax, (-2.35, 2.35), (0, 2.65))
    # White strip makes clear that the finite drawing stops before the boundary.
    ax.axhspan(0, .075, color="white", zorder=4)
    ax.spines["bottom"].set_zorder(5)
    ax.set_xticks([-2, -1, 0, 1, 2])
    ax.set_yticks([1, 2])
    save(fig, "modular-tiling")


if __name__ == "__main__":
    domain()
    tiling()
