#!/usr/bin/env python3
"""Build and audit the formalization modulo explicit literature inputs. No compiled proof oracle is used.

Python orchestrates Lean and checks provenance. Mathematical proof checking
is done by Lean; this script's success is not an unconditional counterexample.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
REPORTS = ROOT/'reports'
ALLOWED_AXIOMS = {'propext','Classical.choice','Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def code_only(s):
    """Remove nested Lean comments and strings before scanning declaration tokens."""
    out=[]; i=0; depth=0
    while i<len(s):
        if depth:
            if s.startswith('/-',i): depth+=1; i+=2
            elif s.startswith('-/',i): depth-=1; i+=2
            else: i+=1
        elif s.startswith('/-',i): depth=1; i+=2
        elif s.startswith('--',i):
            end=s.find('\n',i); i=len(s) if end<0 else end
        elif s[i]=='"':
            i+=1
            while i<len(s):
                if s[i]=='\\': i+=2
                elif s[i]=='"': i+=1; break
                else: i+=1
            out.append(' ')
        else: out.append(s[i]); i+=1
    if depth: raise RuntimeError('Unclosed Lean comment')
    return ''.join(out)

def project_imports(source):
    modules=set()
    for line in code_only(source).splitlines():
        words=line.split()
        if words and words[0]=='import':
            modules.update(m for m in words[1:] if m=='Guralnick' or m.startswith('Guralnick.'))
    return modules

def module_name(path):
    return '.'.join(path.relative_to(ROOT).with_suffix('').parts)

def release_paths():
    # Include the proof/configuration, verification scripts and human audit
    # records. Build outputs and downloaded literature/caches are excluded.
    paths=[ROOT/'Guralnick.lean', ROOT/'GuralnickAudit.lean',
           *sorted((ROOT/'Guralnick').rglob('*.lean')),
           ROOT/'lakefile.toml', ROOT/'lake-manifest.json', ROOT/'lean-toolchain',
           *sorted((ROOT/'scripts').rglob('*.py')),
           *sorted((ROOT/'scripts').rglob('*.sh')),
           *sorted(ROOT.glob('*.md')),
           *sorted((ROOT/'certificates').glob('*.json'))]
    return sorted(set(paths))

def release_snapshot():
    return {str(p.relative_to(ROOT)):sha(p) for p in release_paths()}

def reviewed_inputs():
    """Check the explicitly reviewed files, without rewriting old provenance.

    The formalization is buildable without its manuscript. In that case
    record the absence, rather than claim the manuscript was checked.
    A present but changed file always requires a new human comparison.
    """
    review=json.loads((ROOT/'certificates/manuscript-review.json').read_text())
    result={}
    for item in review['files']:
        path=ROOT/item['path']
        actual=sha(path) if path.is_file() else None
        assert actual is None or actual==item['sha256'], (
            f'Reviewed input changed: {item["path"]}; compare it before updating the review manifest')
        result[item['path']]=dict(expected_sha256=item['sha256'],actual_sha256=actual,
                                 present=actual is not None)
    return result

def run(args, log):
    r=subprocess.run(args,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (REPORTS/log).write_text(r.stdout)
    if r.returncode:
        print(r.stdout)
        raise RuntimeError(f'Failed: {args}; see reports/{log}')
    return r.stdout

def main():
    if sys.flags.optimize:
        raise RuntimeError('Run verification without -O: provenance checks use assertions')
    REPORTS.mkdir(exist_ok=True)
    initial_release_hashes=release_snapshot()
    initial_reviewed_inputs=reviewed_inputs()
    sources=[ROOT/'Guralnick.lean', ROOT/'GuralnickAudit.lean',
             *sorted((ROOT/'Guralnick').rglob('*.lean'))]
    forbidden=re.compile(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b')
    for p in sources:
        match=forbidden.search(code_only(p.read_text()))
        if match: raise RuntimeError(f'Forbidden proof escape {match[0]} in {p.name}')
    imports=project_imports((ROOT/'Guralnick.lean').read_text())
    expected_modules={module_name(p) for p in (ROOT/'Guralnick').rglob('*.lean')}
    audit_modules={'Guralnick.AxiomAudit', 'Guralnick.GuardedAudit'}
    audit_imports=project_imports((ROOT/'GuralnickAudit.lean').read_text())
    assert audit_imports == audit_modules, 'Audit target must build both audits'
    assert not (audit_modules & imports), 'Mathematical library imports audit commands'
    assert expected_modules == imports | audit_imports, (
        'Unbuilt or unexpected project modules', expected_modules ^ (imports | audit_imports))
    library_modules=expected_modules-audit_modules
    for module in library_modules:
        path=ROOT/(module.replace('.', '/')+'.lean')
        used=project_imports(path.read_text())
        assert not (used & audit_modules), f'Library module {module} imports audit commands'
    diagnostic=(ROOT/'Guralnick/AxiomAudit.lean').read_text()
    guarded=(ROOT/'Guralnick/GuardedAudit.lean').read_text()
    diagnostic_names=re.findall(r'^#print axioms (\S+)',diagnostic,re.M)
    guarded_names=re.findall(r'^#print axioms (\S+)',guarded,re.M)
    assert len(set(diagnostic_names)) == len(diagnostic_names), 'Duplicate diagnostic check'
    assert diagnostic_names == guarded_names, 'Diagnostic and guarded axiom checks differ'
    seed_declarations = {
        'Guralnick.SeedPolynomials.rank_one_polynomial',
        'Guralnick.SeedPolynomials.diagonal_polynomial',
        'Guralnick.SeedPolynomials.four_web_identity',
    }
    assert seed_declarations <= set(guarded_names), 'Actual seed identities missing from guarded audit'
    interface_names=re.findall(r'^#print (?!axioms)(\S+)',guarded,re.M)
    assert guarded.count('#guard_msgs (whitespace := lax) in') == (
        len(guarded_names)+len(interface_names))
    lake_config=(ROOT/'lakefile.toml').read_text()
    assert 'defaultTargets = ["Guralnick", "GuralnickAudit"]' in lake_config, (
        'Default build must build both library and audit targets')
    final_module='Guralnick.ModelComparisonCounterexample'
    seen=set(); todo=[final_module]
    while todo:
        module=todo.pop()
        if module in seen: continue
        seen.add(module)
        module_file=ROOT/(module.replace('.','/')+'.lean')
        if module_file.exists():
            todo.extend(project_imports(module_file.read_text()))
    assert {'Guralnick.WebGraphProof','Guralnick.WebFamilyEvaluation','Guralnick.WebTrace',
            'Guralnick.Web'} <= seen, 'Graph interpretation missing from final proof imports'
    comparison_modules={
        'Guralnick.PolynomialWebLiterature','Guralnick.PolynomialFlagConvolution',
        'Guralnick.PolynomialOrbitTransfer','Guralnick.PolynomialLatticeBasis',
        'Guralnick.PolynomialFlags','Guralnick.LatticeEquivariance',
        'Guralnick.PolynomialCoordinateFlags','Guralnick.CoordinateLatticeDegree',
        'Guralnick.CoordinateLiteratureTransfer','Guralnick.RationalCoordinateH1',
        'Guralnick.RationalCoordinateRepresentations','Guralnick.SLCoordinateReduced',
        'Guralnick.SLCoordinateHopf'}
    assert comparison_modules <= seen, f'Model comparison absent from final imports: {comparison_modules-seen}'
    elementary_modules={
        'Guralnick.KLInversion','Guralnick.AffineAdjacentInversions',
        'Guralnick.OrbitMatrixLengthConsequences','Guralnick.ElementaryCoxeterParabolic',
        'Guralnick.ElementaryCoxeterFinite','Guralnick.ElementaryCoxeterDiagram',
        'Guralnick.FiniteFlagEnumeration','Guralnick.PolynomialOrbitCounting',
        'Guralnick.CoordinateSubspaceQuotient','Guralnick.SphericalMergeConstruction',
        'Guralnick.FiniteSymmetrizerEigen','Guralnick.FiniteSymmetrizerAbsorption',
        'Guralnick.ElementaryCoxeterBlockLength','Guralnick.ParabolicStandardSum',
        'Guralnick.ParabolicCosetFactorization','Guralnick.ParabolicIdealInclusion',
        'Guralnick.PolynomialConvolutionConstruction','Guralnick.FiniteFlagExtension',
        'Guralnick.PolynomialFlagExtension','Guralnick.ParabolicFlagStabilizer',
        'Guralnick.PolynomialFullGalleryEquiv','Guralnick.PolynomialFullGalleryCardinality',
        'Guralnick.PolynomialFullLiftCardinality','Guralnick.FullFlagHeckeCounting',
        'Guralnick.PolynomialConvolutionNormalization','Guralnick.OrbitDimensionLength',
        'Guralnick.CanonicalSchurFromRefinement','Guralnick.SchurCornerEigen',
        'Guralnick.HeckeEigenCoordinates','Guralnick.KLDerivedBar','Guralnick.FamilyNontriviality'}
    assert elementary_modules <= seen, f'Elementary reductions absent from final imports: {elementary_modules-seen}'
    (REPORTS/'fidelity-import-closure.json').write_text(json.dumps(dict(
        target=final_module,project_module_count=len(seen),modules=sorted(seen),
        graph_imported='Guralnick.Web' in seen,web_masks_imported='Guralnick.WebMasks' in seen,
        fixed_graph_evaluation_imported='Guralnick.WebFamilyEvaluation' in seen,
        model_comparisons_imported=sorted(comparison_modules),
        elementary_reductions_imported=sorted(elementary_modules),
        note='Import check, not a substitute for the graph-evaluation and model-comparison theorems.'),indent=2)+'\n')
    manifest=json.loads((ROOT/'lake-manifest.json').read_text())
    mathlib=next(p for p in manifest['packages'] if p['name']=='mathlib')
    assert mathlib['rev']=='49af9b7fd7e19db08a946b5bd08d1a5bc39dfd3d'
    assert all(p['type']=='git' and re.fullmatch('[0-9a-f]{40}',p['rev']) for p in manifest['packages'])
    dependency_checks=[]
    packages_dir=ROOT/manifest['packagesDir']
    for package in manifest['packages']:
        checkout=packages_dir/package['name']
        assert not checkout.is_symlink(), f'Symlinked dependency: {package["name"]}'
        actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=checkout,text=True).strip()
        assert actual==package['rev'], f'Wrong pinned checkout: {package["name"]}'
        # Check staged and unstaged tracked edits while leaving ignored
        # dependency/build caches alone. This is a read-only provenance check.
        dirty=subprocess.check_output(
            ['git','status','--porcelain','--untracked-files=no'],cwd=checkout,text=True)
        assert not dirty.strip(), f'Tracked dependency modifications in {package["name"]}:\n{dirty}'
        dependency_checks.append(dict(name=package['name'],rev=actual,tracked_sources_clean=True))
    (REPORTS/'dependency-checks.json').write_text(json.dumps(dependency_checks,indent=2)+'\n')
    assert (ROOT/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.22.0-rc2'

    generated=[ROOT/'Guralnick/WindowExamples.lean',ROOT/'certificates/windows.json']
    before={str(p.relative_to(ROOT)):sha(p) for p in generated}
    run([sys.executable,'scripts/generate_windows.py'],'generate-windows.txt')
    assert before=={str(p.relative_to(ROOT)):sha(p) for p in generated}, 'Generator changed committed certificates'

    inventory=json.loads((ROOT/'certificates/source-inventory.json').read_text())
    for item in inventory:
        if 'copy' in item: assert sha(ROOT/item['copy'])==item['sha256'], item['copy']
    manuscript_unchanged=True if initial_reviewed_inputs['../main.tex']['present'] else None
    if (ROOT.parent/'main_old.tex').exists():
        assert sha(ROOT.parent/'main_old.tex')==inventory[0]['sha256'], (
            'Previous manuscript no longer matches the historical source inventory')

    print('Building the mathematical library and verification targets...',flush=True)
    run(['lake','build','Guralnick','GuralnickAudit'],'lake-build.txt')
    print('Checking failing axiom guards and exact theorem interfaces...',flush=True)
    run(['lake','env','lean','Guralnick/GuardedAudit.lean'],'guarded-audit.txt')
    print('Checking negative controls for the audit mechanism...',flush=True)
    run([sys.executable,'scripts/check_guard_failures.py'],'negative-audit-checks.txt')
    print('Checking principal theorem axioms...',flush=True)
    audit=run(['lake','env','lean','Guralnick/AxiomAudit.lean'],'axioms.txt')
    dependencies={name:[a.strip() for a in axioms.split(',') if a.strip()]
        for name,axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit)}
    for name in re.findall(r"'([^']+)' does not depend on any axioms",audit): dependencies[name]=[]
    expected=(ROOT/'Guralnick/AxiomAudit.lean').read_text().count('#print axioms ')
    assert len(dependencies)==expected, (len(dependencies),expected)
    for name,axioms in dependencies.items():
        extra=set(axioms)-ALLOWED_AXIOMS
        assert not extra, f'Unexpected axioms for {name}: {extra}'

    # A content-addressed source manifest works even outside a Git checkout.
    # It records exactly the proof sources, pinned configuration and verifier;
    # retaining this manifest with the logs identifies the checked revision.
    release_hashes=release_snapshot()
    assert release_hashes==initial_release_hashes, (
        'Proof/configuration/audit sources changed during verification; rerun after edits finish')
    assert reviewed_inputs()==initial_reviewed_inputs, 'Reviewed inputs changed during verification'
    canonical_manifest=json.dumps(release_hashes,sort_keys=True,separators=(',',':'))
    source_revision=hashlib.sha256(canonical_manifest.encode()).hexdigest()
    (REPORTS/'source-manifest.json').write_text(json.dumps(dict(
        sha256=source_revision, files=release_hashes,
        algorithm='SHA-256 of UTF-8 JSON files map, sorted keys, compact separators'),
        indent=2)+'\n')

    summary=dict(status='fixed graph, six-map argument, polynomial/completed flags and coordinate-cohomology comparisons proved modulo explicit general literature inputs; not unconditional',
        lake_build=True,build_targets=['Guralnick','GuralnickAudit'],
        library_excludes_audit_targets=True,all_modules_imported=True,
        lean_sources=len(sources),principal_declarations_audited=len(dependencies),
        guarded_axiom_checks=len(guarded_names),
        guarded_assumption_interfaces=interface_names,
        negative_audit_controls_rejected=True,
        guarded_endpoint_interfaces=['finalStatement','rowStatement','namedFamilyStatement',
            'seedRankOnePolynomialStatement','seedDiagonalPolynomialStatement'],
        source_revision_sha256=source_revision,
        release_sources_unchanged_during_verification=True,
        pinned_dependency_checkouts=dependency_checks,
        allowed_foundational_axioms=sorted(ALLOWED_AXIOMS),additional_axioms=[],
        native_decide_used=False,certificate_regeneration_identical=True,
        final_endpoint=final_module+'.not_absoluteBoundedness',
        named_family_endpoint=final_module+'.named_row_and_lower_bound',
        polynomial_completed_lattice_equivalence=True,
        polynomial_completed_flag_gallery_equivalence=True,
        canonical_coordinate_flag_realization_proved=True,
        fixed_endpoint_gallery_finiteness_proved=True,
        orbit_coordinate_completion_transport=True,
        standard_sl_coordinate_ring_and_hopf_structure=True,
        rational_representation_comodule_comparison=True,
        regular_cochain_tensor_h1_comparison=True,
        full_flag_bruhat_hecke_realization_kernel_proved=False,
        partial_convolution_derived_from_binary_full_flag=True,
        actual_full_refinements_and_fiber_counts_proved=True,
        matrix_dimension_identity_proved_from_inversions=True,
        canonical_eigen_corner_reduction_proved=True,
        schur_support_derived_from_refinement=True,
        polynomial_web_literature_fields=['refinement','full_flag'],
        bar_involutivity_derived=True,
        family_finite_action_nontriviality_proved=True,
        andersen_h1_finiteness_assumed=False,
        finite_flag_enumeration_proved=True,
        derived_rational_cohomology_theorem_kernel_proved=False,
        graph_evaluation_formalized=True,
        graph_evaluation_scope='fixed checked graph presentation; not a global annular isotopy quotient',
        graph_morphism_equality_formalized=True,
        graph_bridge_in_final_import_closure=True,
        global_annular_quotient_formalized=False,full_seed_kl_identity_certified=True,
        seed_kl_proof_method='actual canonical web identities and KL normalization; kernel checked',
        seed_additional_mathematical_assumptions=[],
        seed_kl_declarations=['Guralnick.SeedPolynomials.rank_one_polynomial',
            'Guralnick.SeedPolynomials.diagonal_polynomial'],
        actual_seed_web_coordinates_proved=[
            'SeedWebCoordinates.raw_source','SeedRankOne.raw_source',
            'SeedWebCoordinates.one_line_source','SeedWebCoordinates.reflected_one_line_source',
            'SeedWebCoordinates.corrected_graph_source'],
        experimental_audit_scripts_are_proofs=False,
        manuscript_unchanged=manuscript_unchanged,
        manuscript_review='certificates/manuscript-review.json',
        reviewed_inputs=initial_reviewed_inputs,
        source_hashes={str(p.relative_to(ROOT)):sha(p) for p in sources},
        dependencies=dependencies)
    (REPORTS/'verification.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(f'PASS: {len(sources)} Lean sources built; {len(dependencies)} principal declarations audited.')
    print('Only standard foundational axioms. Final counterexample remains conditional.')

if __name__=='__main__': main()
