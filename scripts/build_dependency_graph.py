#!/usr/bin/env python3
"""Render the reviewed dependency ledger with Graphviz (no certification inference).

Run from any directory: python3 scripts/build_dependency_graph.py
Numbered-result pictures suppress transitive edges while retaining prerequisite
reachability. The complete DOT records every numbered/auxiliary/source edge in
the ledger. Definitions and library infrastructure remain in the JSON inventory.
"""
from __future__ import annotations
import collections
import html
import json
from pathlib import Path
import subprocess
import textwrap

ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / 'docs'
SOURCE = ROOT / 'certification/dependency_inventory.json'
STATUS = ROOT / 'certification/status.json'
URL = 'https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/main/'

STATUS_COLORS = {
    'Pending': ('#fff4dc', '#b88023'),
    'Active': ('#fff6b0', '#8b7516'),
    'Partial': ('#e4f1ff', '#3676aa'),
    'Certified': ('#e1f5df', '#408342'),
}


def status_summary(rows):
    counts = collections.Counter(r.get('status', 'Pending') for r in rows)
    return '; '.join(f'{counts[s]} {s.lower()}' for s in
                     ['Certified', 'Partial', 'Active', 'Pending'] if counts[s])


def status_attributes(status):
    fill, border = STATUS_COLORS[status]
    return ', fillcolor='+q(fill)+', color='+q(border)

SHORT = {
 'lem:delta':'Delta identity and support',
 'lem:integrals':'Localized integral estimates',
 'lem:quadriccount':'Integer zeros of a quadric',
 'lem:polynomialbox':'Polynomial congruences in boxes',
 'lem:weil':'Weil character-sum bound',
 'cor:weilline':'Projective-line bound',
 'lem:katz':'Katz bound on the quadric',
 'lem:crt':'CRT and scalar invariance',
 'lem:gauss':'Gauss sums and point count',
 'lem:badprime':'Bound at bad primes',
 'lem:ramified':'Shared-prime identity',
 'lem:goodglobal':'Global formula and cone ratio',
 'lem:genericmod':'Off-cone modulus sum',
 'lem:conemod':'Cancellation on the cone',
 'lem:density':'Local densities',
 'lem:singseries':'Singular series and tail',
 'lem:box':'Exceptional congruence count',
 'lem:average':'Average over exceptional frequencies',
 'lem:exceptional':'Bad primes and exceptional planes',
 'lem:conic':'Conic parametrization',
 'lem:section':'Plane-section character sum',
 'lem:fourier':'Uniform Fourier bound',
 'lem:diagbad':'Diagonal bad-prime criterion',
 'lem:pencil':'Exact diagonal pencil formula',
 'prop:analytic':'Uniform analytic asymptotic',
 'lem:poisson':'Delta-Poisson formula',
 'lem:offcone':'Off-cone contribution',
 'lem:oncone':'Nonzero cone contribution',
 'lem:zerofreq':'Zero-frequency main term',
 'lem:annulus':'Uniform annular estimate',
 'lem:charsum':'Character-weight specialization',
 'cor:centered':'Centered correlations',
 'lem:sieve':'Uniform power sieve',
 'lem:divisible':'Divisibility of quadratic trace',
 'lem:lowerbeta':'Lower bounds for local factors',
 'cor:relative':'Ranges for relative asymptotics',
 'thm:polynomial':'Quadratic-character asymptotic',
 'thm:uniformcount':'Uniform square-value count',
 'thm:diagonal':'Explicit diagonal local factors',
 'thm:cyclic':'Higher-order characters',
 'cor:powercount':'Uniform power-value count',
 'prop:salberger':'Determinant-method comparison',
}
SECTION_NAMES = {
 1:'Main results (Section 1)', 2:'Preliminary lemmas (Section 2)',
 3:'Local sums (Section 3)', 4:'Fourier transforms (Section 4)',
 5:'Analytic assembly and consequences (Section 5)',
 6:'Fixed forms (Section 6)',
}
EXTERNAL_GROUPS = {
 'HB':'Heath-Brown\nDelta symbol, integrals, Poisson',
 'MV':'Montgomery-Vaughan\nGauss, Ramanujan, L-series, primes',
 'FINITE':'Weil and Katz\nFinite-field character sums',
 'GEOMETRY':'Lang and Hartshorne\nElimination, Bertini, cyclotomic fields',
 'S':'Salberger\nComplete intersections and lines',
}
OVERVIEW_GROUPS = [
 ('prelim','Preliminary tools','Lemmas 2.1-2.4',
  ['lem:delta','lem:integrals','lem:quadriccount','lem:polynomialbox']),
 ('finite','Finite-field estimates','Lemmas 2.5, 2.7; Corollary 2.6',
  ['lem:weil','cor:weilline','lem:katz']),
 ('local','Local arithmetic','Lemmas 3.1-3.11',
  ['lem:crt','lem:gauss','lem:badprime','lem:ramified','lem:goodglobal','lem:genericmod','lem:conemod','lem:density','lem:singseries','lem:box','lem:average']),
 ('fourier','Geometric Fourier bounds','Lemmas 4.1-4.6',
  ['lem:exceptional','lem:conic','lem:section','lem:fourier','lem:diagbad','lem:pencil']),
 ('analytic','Analytic assembly','Proposition 5.1; Lemmas 5.1-5.5',
  ['prop:analytic','lem:poisson','lem:offcone','lem:oncone','lem:zerofreq','lem:annulus']),
 ('characters','Character specialization','Lemma 5.6',['lem:charsum']),
 ('sieve','Power sieve','Lemma 5.8',['lem:sieve']),
 ('consequences','Further consequences','Corollaries 5.7, 5.11; Lemmas 5.9, 5.10',
  ['cor:centered','lem:divisible','lem:lowerbeta','cor:relative']),
 ('maincharacters','Character-sum theorems','Theorems 1.1, 1.3, 1.4',
  ['thm:polynomial','thm:diagonal','thm:cyclic']),
 ('mainpowers','Power-value counts','Theorem 1.2; Corollary 1.1',
  ['thm:uniformcount','cor:powercount']),
 ('fixed','Determinant comparison','Proposition 6.1',['prop:salberger']),
]


def q(s):
    return json.dumps(str(s), ensure_ascii=False)


def ids(values):
    return [x.get('label', x.get('id')) if isinstance(x, dict) else x for x in (values or [])]


def row_id(row):
    return row.get('label', row.get('id'))


def number_key(row):
    return tuple(int(x) for x in row['number'].split('.')) + (row['kind'],)


def source_link(row):
    loc = row.get('statement_lines') or row.get('source_lines')
    if not loc and row.get('source_ranges'):
        loc = row['source_ranges'][0]
    if loc:
        return URL + 'manuscript/quadratic_character_sums_github.tex#L%d-L%d' % tuple(loc)
    return URL + 'certification/dependency_inventory.json'


def group_of_external(key):
    if key.startswith('EXT.HB') or key == 'EXT.POISSON_R4': return 'HB'
    if key.startswith('EXT.MV'): return 'MV'
    if key in ['EXT.WEIL','EXT.KATZ']: return 'FINITE'
    if key.startswith('EXT.LANG') or key.startswith('EXT.HARTSHORNE'): return 'GEOMETRY'
    if key.startswith('EXT.SALBERGER'): return 'S'
    return key


def adjacency(nodes, edges):
    out = {n:set() for n in nodes}
    for a,b in edges:
        if a not in out or b not in out: raise ValueError(f'Unknown dependency edge {a} -> {b}')
        out[a].add(b)
    return out


def topological(nodes, edges):
    out = adjacency(nodes, edges)
    indeg={n:0 for n in nodes}
    for vs in out.values():
        for v in vs: indeg[v]+=1
    ready=sorted(n for n,k in indeg.items() if k==0)
    ordered=[]
    while ready:
        u=ready.pop(0); ordered.append(u)
        for v in sorted(out[u]):
            indeg[v]-=1
            if indeg[v]==0: ready.append(v);ready.sort()
    if len(ordered)!=len(nodes):
        raise ValueError('Cycle in plotted dependency relation: '+str([n for n,k in indeg.items() if k]))
    return ordered


def transitive_reduction(nodes, edges):
    edges=set(edges); topological(nodes,edges)
    out=adjacency(nodes,edges)
    result=set()
    for a,b in edges:
        todo=list(out[a]-{b}); seen=set(); alternate=False
        while todo:
            v=todo.pop()
            if v==b: alternate=True; break
            if v in seen: continue
            seen.add(v); todo.extend(out[v]-seen)
        if not alternate: result.add((a,b))
    return result


def all_dependencies(row):
    deps=ids(row.get('principal_internal_dependencies', row.get('internal_dependencies', [])))
    deps+=ids(row.get('auxiliary_dependencies', []))
    deps+=ids(row.get('external_inputs', []))
    return deps


def project_numbered(rows, auxiliaries, external):
    """Collapse auxiliary nodes to their nearest numbered/source prerequisites."""
    rowmap={r['label']:r for r in rows}; auxmap={r['id']:r for r in auxiliaries}
    allmap={**rowmap,**auxmap}
    numbered_edges=set(); source_edges=set(); via_aux=set()
    def walk(dep, target, chain=()):
        if dep in chain: raise ValueError('Auxiliary dependency cycle: '+str(chain+(dep,)))
        if dep in rowmap:
            if dep!=target:
                numbered_edges.add((dep,target))
                if chain:via_aux.add((dep,target))
        elif dep in external:
            source_edges.add((dep,target))
        elif dep in auxmap:
            for child in all_dependencies(auxmap[dep]): walk(child,target,chain+(dep,))
        else: raise ValueError(f'Unknown dependency {dep} for {target}')
    for r in rows:
        for dep in all_dependencies(r): walk(dep,r['label'])
    topological(rowmap,numbered_edges)
    return numbered_edges,source_edges,via_aux


def html_label(title, body, status=None, width=27):
    lines=textwrap.wrap(body,width=width,break_long_words=False,break_on_hyphens=False)
    text='<B>'+html.escape(title)+'</B>'
    if lines:text+='<BR/>'+ '<BR/>'.join(html.escape(x) for x in lines)
    if status:text+='<BR/><FONT POINT-SIZE="10" COLOR="'+STATUS_COLORS[status][1]+'">['+html.escape(status)+']</FONT>'
    return '<'+text+'>'


def header(name,title,subtitle,overview=False):
    font=14 if overview else 12
    return [
        'digraph '+name+' {',
        'graph [rankdir=TB, newrank=true, compound=true, outputorder=edgesfirst,',
        '  bgcolor="white", fontname="DejaVu Serif", fontsize=23, labelloc=t,',
        '  label='+q(title+'\n'+subtitle)+',',
        '  nodesep=0.30, ranksep=0.58, pad=0.28, splines=polyline];',
        f'node [shape=box, style="rounded,filled", fillcolor="#fff4dc", color="#b88023",',
        f'  fontname="DejaVu Serif", fontsize={font}, penwidth=1.15, margin="0.12,0.09"];',
        'edge [color="#4b5563", arrowsize=0.70, penwidth=1.05];',
    ]


def write_numbered(data, edges, sources, via_aux):
    rows=data['results']; rowmap={r['label']:r for r in rows}
    reduced=transitive_reduction(rowmap,edges)
    status=status_summary(rows)
    dot=header('NumberedResults','Dependency graph for the numbered results',
        'Frozen v35 | '+status+'\nLiterature inputs trusted; Lean interfaces pending registration')
    source_groups=sorted({group_of_external(k) for k,_ in sources})
    dot.append('subgraph cluster_sources { label="Trusted reference inputs (assumed, not reproved)"; fontsize=15; color="#a59adc"; style="rounded"; rank=same;')
    for group in source_groups:
        text=EXTERNAL_GROUPS.get(group,group)
        dot.append(q('source:'+group)+' [label='+q(text)+', fillcolor="#eeeafd", color="#7762b4", fontsize=11];')
    dot.append('}')
    for r in rows:
        name=r['kind'].capitalize()+' '+r['number']; lab=r['label']
        current=r.get('status','Pending')
        dot.append(q(lab)+' [label='+html_label(name,SHORT[lab],current)+status_attributes(current)+', URL='+q(source_link(r))+', target="_blank", tooltip='+q(r['content'])+'];')
    # These equal-rank layout constraints are not additional dependency edges.
    # Every displayed arrow below comes from the reviewed ledger.
    ranks=[
        ['lem:delta','lem:quadriccount','lem:polynomialbox','lem:weil','lem:katz'],
        ['lem:integrals','cor:weilline','lem:crt','lem:gauss','lem:badprime'],
        ['lem:ramified','lem:box','lem:density','lem:exceptional','lem:conic'],
        ['lem:goodglobal','lem:conemod','lem:average','lem:section','lem:diagbad'],
        ['lem:genericmod','lem:singseries','lem:fourier','lem:poisson','prop:salberger'],
        ['lem:pencil','lem:offcone','lem:oncone','lem:zerofreq','lem:divisible'],
        ['lem:annulus'],['prop:analytic'],['lem:charsum'],
        ['thm:polynomial','thm:cyclic','lem:sieve','lem:lowerbeta'],
        ['thm:diagonal','cor:centered','thm:uniformcount','cor:powercount','cor:relative'],
    ]
    assert {x for rank in ranks for x in rank}==set(rowmap)
    for rank in ranks: dot.append('{rank=same; '+'; '.join(q(x) for x in rank)+';}')
    for a,b in sorted(reduced):
        attr=''
        if (a,b) in via_aux and a not in ids(rowmap[b].get('principal_internal_dependencies')):
            attr=' [style=dashed, color="#7a8795", tooltip="Through an unnumbered proof obligation; see full ledger"]'
        dot.append(q(a)+' -> '+q(b)+attr+';')
    # Avoid repeated references within a source family at each target.
    for a,b in sorted({('source:'+group_of_external(k),target) for k,target in sources}):
        dot.append(q(a)+' -> '+q(b)+' [style=dashed, color="#8d79bc", penwidth=0.9, tooltip="Trusted literature input (possibly through a registered auxiliary target)"];')
    dot.append('legend [shape=plain, style="", label='+q('Solid: numbered prerequisite. Gray dashed: through an unnumbered proof step.\nPurple dashed: trusted source. Transitive numbered edges are omitted.\n'+status+'. Partial means identified clauses checked; the full result is unfinished.\nClick a result for its manuscript statement. Full details are in the dependency inventory.')+', fontsize=11];')
    dot.append('{rank=sink; legend;}')
    for node in sorted(set(rowmap)-{a for a,b in reduced}):
        dot.append(q(node)+' -> legend [style=invis];')
    dot.append('}')
    path=DOCS/'dependency_graph.dot';path.write_text('\n'.join(dot)+'\n')
    return path,dict(numbered_nodes=len(rows),numbered_edges=len(edges),displayed_numbered_edges=len(reduced),source_edges=len(sources))


def write_overview(data, edges, sources):
    rowmap={r['label']:r for r in data['results']}
    membership={r:g for g,_,_,rs in OVERVIEW_GROUPS for r in rs}
    if set(membership)!=set(rowmap): raise ValueError('Overview group membership does not match numbered inventory.')
    groupnodes={g for g,_,_,_ in OVERVIEW_GROUPS}
    gedges={(membership[a],membership[b]) for a,b in edges if membership[a]!=membership[b]}
    reduced=transitive_reduction(groupnodes,gedges)
    dot=header('Overview','Proof structure of the quadratic-forms paper',
               'Frozen v35 | '+status_summary(data['results'])+' | Source-relative Lean certification',True)
    dot.append('sources [label='+q('Trusted reference inputs\nHeath-Brown; Weil and Katz; Montgomery-Vaughan;\nLang; Hartshorne; Salberger')+', fillcolor="#eeeafd", color="#7762b4", fontsize=14];')
    for group,title,subtitle,members in OVERVIEW_GROUPS:
        member_rows=[rowmap[x] for x in members]
        states={r.get('status','Pending') for r in member_rows}
        current=next((s for s in ['Partial','Active','Pending','Certified'] if s in states))
        lab='<B>'+html.escape(title)+'</B><BR/>'+html.escape(subtitle)+'<BR/><FONT POINT-SIZE="12" COLOR="'+STATUS_COLORS[current][1]+'">'+html.escape(status_summary(member_rows))+'</FONT>'
        dot.append(q(group)+' [label=<'+lab+'>'+status_attributes(current)+', URL='+q(URL+'INVENTORY.md')+', target="_blank"];')
    for a,b in sorted(reduced):dot.append(q(a)+' -> '+q(b)+' [penwidth=1.4];')
    for group in sorted({membership[b] for _,b in sources}):
        dot.append('sources -> '+q(group)+' [style=dashed, color="#8d79bc", penwidth=1.0];')
    dot.append('legend [shape=plain, style="", label='+q('Boxes group the numbered results listed inside them.\nArrows record prerequisites between groups; transitive group edges are omitted.\nThe full graph shows all 42 results separately.\nCompletion requires Lean execution and a review of the formal statements.')+', fontsize=12];')
    dot.append('{rank=sink; legend;}')
    for node in sorted(groupnodes-{a for a,b in reduced}):
        dot.append(q(node)+' -> legend [style=invis];')
    dot.append('}')
    path=DOCS/'dependency_overview.dot';path.write_text('\n'.join(dot)+'\n');return path


def write_complete(data):
    rows=data['results'];aux=data['auxiliary_obligations'];external=data['external_input_catalog']
    dot=header('CompleteLedger','Complete recorded dependency ledger','Numbered results, auxiliary obligations, and trusted reference interfaces')
    nodes=set();edges=set()
    for r in rows+aux:
        rid=row_id(r);nodes.add(rid)
        title=(r['kind'].capitalize()+' '+r['number']) if 'label' in r else rid
        attr=status_attributes(r.get('status','Pending'))
        dot.append(q(rid)+' [label='+html_label(title,SHORT.get(rid,r['content']),r.get('status','Pending'),width=34)+attr+', URL='+q(source_link(r))+'];')
        for dep in all_dependencies(r):edges.add((dep,rid))
    for key,item in external.items():
        nodes.add(key)
        label=key+'\n'+item.get('locator','')
        dot.append(q(key)+' [label='+q(label)+', fillcolor="#eeeafd", color="#7762b4"];')
    topological(nodes,edges)
    for a,b in sorted(edges):dot.append(q(a)+' -> '+q(b)+(' [style=dashed, color="#8d79bc"]' if a in external else '')+';')
    dot.append('// Foundation/library requirements and exact definitions are retained in the JSON ledger, not promoted to source axioms.')
    dot.append('}')
    path=DOCS/'dependency_complete.dot';path.write_text('\n'.join(dot)+'\n');return path,len(nodes),len(edges)


def render(path):
    for fmt in ['svg','pdf','png']:
        target=path.with_suffix('.'+fmt)
        options=['-Gdpi=105'] if fmt=='png' else []
        subprocess.run(['dot','-T'+fmt,*options,str(path),'-o',str(target)],check=True)


def main():
    DOCS.mkdir(exist_ok=True)
    data=json.loads(SOURCE.read_text())
    live=json.loads(STATUS.read_text())
    for row in data['results']:
        row['status']=live['numbered_results'][row['label']]['status']
    for row in data['auxiliary_obligations']:
        row['status']=live['supplementary_groups'][row['id']]['status']
    rows=data['results']
    if len(rows)!=42:raise ValueError('Expected the frozen v35 register of exactly 42 numbered results.')
    edges,sources,via_aux=project_numbered(rows,data['auxiliary_obligations'],data['external_input_catalog'])
    full,counts=write_numbered(data,edges,sources,via_aux)
    overview=write_overview(data,edges,sources)
    complete,totalnodes,totaledges=write_complete(data)
    render(overview);render(full)
    print(json.dumps({'source_sha256':data['source_sha256'],**counts,'complete_ledger_nodes':totalnodes,'complete_ledger_edges':totaledges,'outputs':[str(overview.relative_to(ROOT)),str(full.relative_to(ROOT)),str(complete.relative_to(ROOT))]},indent=2))

if __name__=='__main__':main()
