"""Build a scoped, reproducible coverage ledger from the published 207-card archive."""
from pathlib import Path
from html.parser import HTMLParser
import json, hashlib, re, collections, zipfile, html, argparse
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'atlas/coverage'
p=argparse.ArgumentParser();p.add_argument('--source-archive',type=Path,required=True);p.add_argument('--zenodo-metadata',type=Path,default=OUT/'zenodo_record.json');p.add_argument('--guards',type=Path,default=OUT/'application_guards.json');a=p.parse_args()
ARCHIVE=a.source_archive
ZEN=json.loads(a.zenodo_metadata.read_text())
class Node:
 def __init__(self,tag='',attrs=()):self.tag=tag;self.attrs=dict(attrs);self.children=[]
 def text(self):return re.sub(r'\s+',' ',''.join(c.text() if isinstance(c,Node) else c for c in self.children)).strip()
 def has(self,cl):return cl in self.attrs.get('class','').split()
 def find(self,cl):
  if self.has(cl):return self
  for c in self.children:
   if isinstance(c,Node):
    v=c.find(cl)
    if v:return v
 def all(self,cl):return ([self]if self.has(cl)else[])+[v for c in self.children if isinstance(c,Node) for v in c.all(cl)]
class DOM(HTMLParser):
 def __init__(self):super().__init__(convert_charrefs=True);self.root=Node();self.stack=[self.root]
 def handle_starttag(self,t,a):
  n=Node(t,a);self.stack[-1].children.append(n)
  if t not in ('meta','link','br','hr','img','input','source','wbr'):self.stack.append(n)
 def handle_startendtag(self,t,a):self.stack[-1].children.append(Node(t,a))
 def handle_endtag(self,t):
  for i in range(len(self.stack)-1,0,-1):
   if self.stack[i].tag==t:self.stack=self.stack[:i];break
 def handle_data(self,d):self.stack[-1].children.append(d)
def get(n,c):
 v=n.find(c);return v.text() if v else ''
MAP={}
def add(ids,repo,path,names,scope):
 for i in ids:
  MAP.setdefault(i,[]).append(dict(repository=repo,path=path,declarations=names.split(),scope=scope))
L='dicipler-pixel/relational-atlas-lean';B='RelationalAtlas/Basic.lean';C='RelationalAtlas/AtlasFormalCore.lean'
add([2],L,B,'normal_commutator normal_iff_commute','Exact finite real-matrix commutator identity and normality equivalence.')
add([2,64],L,C,'symmetric_skew_commutator_identity symmetric_skew_commute_gives_zero','Ring commutator identity only; normalized rank-one angle/stress identifications require separate proofs.')
add([6],L,B,'binary_entropy','Scalar binary-entropy properties; the free-fermion entropy construction and spectrum-to-channel interpretation are not proved here.')
add([31],L,B,'offBlock_trace offBlock_eq_zero_iff','Trace and vanishing equivalence for idempotents; Frobenius norm identity is not in these declarations.')
add([31],L,C,'tangent_occupied_block tangent_empty_block tangent_split','Tangent block decomposition under idempotence and the linearized tangent equation; no dynamical convergence claim.')
add([16],L,C,'rankOne_projector_distance','Rank-one projector-distance identity for real unit vectors in dimension two; no general packing theorem.')
add([32],L,C,'gram2_saturation','Coordinate Lagrange identity in the displayed normalization; geometric two-band identification is additional.')
add([39],L,B,'critical_angle complex_angle_sin complex_angle_cos','Critical-angle inequality and complex trigonometric identities; no derivation of a physical transmission model.')
add([48],L,B,'seam_schur','General invertible-block determinant identity; identification of the paper interface with these blocks is additional.')
add([48],L,C,'scalar_schur_complement','One-channel scalar Schur identity with nonzero denominator.')
add([51],L,B,'reciprocal_reduction unit_circle_u u_from_unit_circle','Quartic reduction and both directions of the unit-circle coordinate correspondence; not the knot census/classification.')
add([51],L,C,'reciprocal_quartic_reduction','Real reciprocal-quartic reduction with nonzero t.')
add([56],L,C,'b56_combined_derivative_not_surjective','Corrected rank obstruction R^2 to R^3 only. The published headline that a curve and point do not meet is not certified.')
add([57],L,C,'indefinite_null_direction_exists','Nonzero null vector in x^2-y^2; not construction of a moving biorthogonal projector.')
add([60],L,C,'tangent_dimension_one_factors','Only the arithmetic implication k*q=1 => k=q=1; not the full saturation/equality characterization.')
add([61],L,C,'bohr_rod','Inverse mass algebra under nonzero constants; no empirical mass-running/cosmological prediction.')
add([66],L,B,'gram_det','Exact Gram determinant square; covering-space and branching claims require additional topology.')
add([66],L,C,'gram_det_is_square','Exact Gram determinant square only.')
add([68],L,B,'paired_spectrum','Nonzero opposite-eigenvalue partner under an anticommuting involution; not a derivation of every index/signature/winding claim.')
add([68],L,C,'chiral_eigenvalue_pair','Eigenvector equation only; without involution/injectivity it does not prove the partner nonzero.')
add([74],L,B,'stratum_repels','Conditional scalar turning inequality; conservation law and geometric applicability must be supplied.')
add([74],L,C,'refraction_turning_barrier','Conditional scalar inequality from nonnegative g and s^2<=1.')
add([75],L,B,'middle_cancels','Signs of ordered-spectrum terms under explicit weight/sign hypotheses; opposite signs alone do not imply exact cancellation, and the Euler growth-rate claim is separate.')
add([85],L,C,'rank_one_complex_realpart_det rank_one_complex_realpart_not_definite','Exact negative-square determinant and nonpositivity; covers the displayed algebraic kernel.')
add([90],L,C,'hermitian_soft_lapse open_soft_crosses open_lapse_square','Exact selected normal forms only; not genericity, integrated-distance exponents, physical clock or openness classification.')
def ext(ids,repo,path,names,scope):add(ids,'dicipler-pixel/'+repo,path,names,scope)
ext([1],'iqgt-grassmannian-lean','IqgtGrassmannian/Basic.lean','Q_eq gram_entries gram_det_nonneg metric_control','Finite Gram/QGT inequality under the declared orthogonal-projector/tangent hypotheses; no arbitrary non-Hermitian extension.')
ext([16],'price-of-a-direction-lean','PriceOfDirection/Basic.lean','overlap separation trackable_iff census_depth','Real two-dimensional rank-one overlap, separation, chosen trackability criterion and logarithmic depth; no general census packing theorem.')
ext([19],'price-of-a-direction-lean','PriceOfDirection/Basic.lean','wall_charpoly wall_real_iff wall_complex_iff onset_exact onset_limit','Specified two-by-two wall and onset formulas, including the large-gain limit; not a universal physical threshold.')
ext([35,113],'price-of-a-direction-lean','PriceOfDirection/Basic.lean','K_eigen specProj_sum specProj_entry_tendsto','Explicit two-by-two model: diverging individual projector entry and constant sum; not the general contour-persistence theorem.')
ext([12],'foft-lean','FOFT/Basic.lean','henrici_rate','Trace identity behind the norm-decay derivative only; derivative, time integration and long-time normal limit are not formalized in this file.')
ext([38],'foft-lean','FOFT/Basic.lean','henrici_rate flow_smul','Supporting trace/flow algebra only; isospectral ODE evolution and stress-decay/convergence need additional proofs.')
ext([139],'foft-lean','FOFT/Basic.lean','heff_factor trace_X_zero odd_moment_zero odd_moment_zero_X chiral_pair','Factorization, zero trace, odd chiral moments and one-pair logarithmic identity; not the convergent Mercator/zeta-regularized analytic construction.')
ext([191],'foft-lean','FOFT/Basic.lean','baseline_commutes baseline_selfComm','Scalar baseline commutes and leaves the self-commutator unchanged; the opposite-book shift formula is not proved here.')
ext([45,136],'spectral-stress-lean','SpectralStress/Basic.lean','pairTerm_antisymm sum_rule','Antisymmetry and finite band-sum cancellation for the supplied pair terms; spectral-projector curvature formula/ambient flatness require separate identification.')
ext([82],'spectral-stress-lean','SpectralStress/Basic.lean','factorisation amplitude limiting_spectrum rho_roots','Algebraic factorization and exact arithmetic from supplied rates/cycles; measured asymptotic input and collision continuation are not derived.')
ext([61],'matter-at-a-scale-lean','MatterAtAScale/Basic.lean','rigid_rod closure_mass closure_mass_ratio','Bohr-rod and conditional scaling identities; physical assumptions remain inputs.')
ext([97],'votkp-lean','VOTKP/Smith.lean','smith_identity round_trip positive_radius hyperbolic_length','Positive real Smith/log/tanh coordinate identities; no physical determination of ionization thresholds.')
ext([98],'votkp-lean','VOTKP/Smith.lean','block_succ block_smith oplus_comm oplus_assoc','Finite real ratio composition; optical realization is separately identified.')
ext([98],'votkp-lean','VOTKP/Film.lean','film_is_oplus','Film rational composition is the declared operation; does not identify real atomic and complex optical geometries.')
ext([99],'votkp-lean','VOTKP/Smith.lean','split_log split_step shell_wall shell_wall_values','Screening/shell logarithm split and shell-wall formula given the threshold model.')
ext([100],'votkp-lean','VOTKP/Film.lean','echo_circle circle_identity circle_criterion circle_through_origin one_radius_cannot_decide','Echo identity and general circle criterion are separate proved statements; the combined physical decision theorem is not explicitly bundled in Lean.')
ext([102],'votkp-lean','VOTKP/Smith.lean','round_trip scale_blind','Ratio reconstruction and scale blindness only; full finite binding-energy sum and nuclear-mass ledger are not formalized here.')
ext([103],'votkp-lean','VOTKP/Peel.lean','cumulant_witness','Two concrete channel triples agree in first two cumulants and differ in the third; the general Newton inversion theorem is not proved here.')
ext([105],'votkp-lean','VOTKP/Peel.lean','reduced_associator','Exact reduced-product associator for an additive projection map in a ring.')
ext([137],'nonnormality-connection-energy-lean','NonNormality/SelfCommutator.lean','norm_sq_selfCommutator_div_eight norm_sq_selfCommutator_div_eight_eq_sum_edgeFinset isStarNormal_iff_isParallel','Displayed graph identity and normal iff parallel under Hermitian diagonal blocks and a unitary skew connection; no transient-growth rate is asserted by these statements.')
ext([137],'nonnormality-connection-energy-lean','NonNormality/Holonomy.lean','parallelSectionsEquivHolonomyFixed','Connected-graph parallel sections identified with holonomy-fixed Hermitian matrices; quantitative/example kernel dimensions are additional.')
ext([189,153],'votkp-lean','VOTKP/Smith.lean','smith_identity round_trip','Shared scalar ratio/log/tanh coordinate only; book-energy identity and chain thermodynamic interpretation are not part of these declarations.')
# Explicit scoped mappings added after inspecting the wider paper repositories.
ext([158],'dirac-time-lean','DiracTime/WeakValue.lean','postselected_weak_value_sq weak_value_bound','Weak-value probability bound under the written inner-product and nonzero-overlap hypotheses; no postselection dynamics is derived.')
ext([159],'dirac-time-lean','DiracTime/PathLedger.lean','descent_iff reverse_path_ledger','Endpoint-potential descent equivalent to silent loops in the declared path system; reachability/connectedness assumptions remain explicit.')
ext([160],'dirac-time-lean','DiracTime/CommonClock.lean','common_gap_scaling rate_shift_unique rescale_same_eigenvectors rescale_scales_gaps','Conditional generator/gap equivalence, rate uniqueness and rescaling; a physical time calibration is not supplied.')
ext([160],'dirac-time-lean','DiracTime/MovingFrame.lean','moving_frame_identity common_clock','Instantaneous moving-frame algebra with derivatives and equations supplied; not a global Schrodinger evolution construction.')
ext([104,110,161],'dirac-time-lean','DiracTime/FiniteReturn.lean','silent_forever_iff finite_return_iff','Finite-dimensional discrete-observation return: some nonzero future moment iff one before dim V. B104 still needs the resolvent-transfer identification; B161 still needs its commutator realization.')
ext([161],'dirac-time-lean','DiracTime/ContinuousReturn.lean','hidden_forever_iff','Zero exponential observation for every real time iff all power moments vanish. The stated theorem quantifies over past and future together; a future-only version is not separately stated.')
ext([162],'dirac-time-lean','DiracTime/EntropyLedger.lean','delta_relative_entropy entropy_correlation_identity integrated_second_law','Entropy/correlation algebra and second law under supplied operator/entropy/nonnegativity facts; subsystem entropies are parameters here, not a full reservoir construction.')
ext([108],'dirac-time-lean','DiracTime/EqualEndpointWitness.lean','present_populations_equal expectation_Z later_readout probe_blind_to_supplement','Exact equal-present/opposite-future witness and probe symmetry; not a universal reconstruction theorem.')
ext([111],'dirac-time-lean','DiracTime/FrictionMetric.lean','pair_friction_eq_weighted_metric gibbs_pair_weight_nonneg two_level_population_gap weighted_sum_band','Pairwise reweighted-metric identities and Gibbs weights; the Davies bath and dynamical derivation are not formalized.')
ext([163],'dirac-time-lean','DiracTime/PhaseSilence.lean','silent_sector_iff end_index_mod_p end_index_mod_q','Torus-knot endpoint congruences and the stated silence criterion; not the APS/eta/signature identification or full arc census.')
ext([130],'light-ledger-lean','OpticalMetric.lean','response_is_weighted_metric response_weight_positive matching_null_directions response_lower_bound response_upper_bound','Finite positive-weight optical metric, bounds and common null directions with spectral/gap hypotheses; not a continuum dielectric derivation.')
ext([131],'light-ledger-lean','LightSpectral.lean','secant_div_le_metric static_lower static_sq_le_budget_secant response_bracket','Finite-spectrum subgap secant/static/budget bounds with nonnegative weights and a positive gap; no full continuum spectral-measure extension.')
ext([127],'light-ledger-lean','Rigidity.lean','regularized_pos regulator_cap null_direction inverse_identity antitone_in_singular_value','Regularized scalar singular-value response and cap with positive regulator; operator-model identification remains separate.')
ext([48,175],'light-ledger-lean','LightBridges/Boundary.lean','schur_interior_residual schur_boundary_residual boundary_lift_identity boundary_hermitian_identity cayley_defect_identity boundary_loss_pullback passive_boundary_chain','Finite boundary elimination and passivity/Cayley loss identities under explicit inverse equations; no horizon or general-relativistic boundary realization.')
ext([95,133],'light-ledger-lean','LightBridges/Census.lean','transition_weight_lower transition_census_budget transition_window_iff_weight census_equals_coupling_count projector_block_coupling','Finite transition-window weight bounds and C-C^2=B B^adjoint for a block projector; physical channel and thermodynamic readings remain additional.')
ext([123],'light-ledger-lean','LightBridges/Examples.lean','obliqueP0_idempotent obliqueP1_idempotent oblique_trace_two','Explicit oblique rank-one idempotents with overlap trace two; does not classify all non-Hermitian overlaps.')
ext([124],'gravity-ledger-lean','Gravity.lean','moving_metric_determinant moving_metric_positive_side moving_metric_indefinite_side chart_idempotent chart_trace_one chart_overlap','Explicit moving-wall chart algebra and determinant signs; no universal coincidence/separation theorem for all exceptional points.')
ext([123],'gravity-ledger-lean','GravityOverlap.lean','overlap_exact overlap_quadratic_limit negative_direction_exceeds_cap local_cap_requires_nonnegative','Equal-trace idempotent overlap identity, differentiability-based Taylor limit and local cap implications under stated assumptions.')
ext([22,31],'upg-lean','UPGAlgebra.lean','commutatorC_eq_blocks commutatorC_gram commutatorC_energy feedbackC_equivalences','Adapted complex block commutator Gram, factor-of-two energy and feedback equivalences; no analytic dissipation/dynamics theorem.')
ext([128],'upg-lean','UPGTorusAnchor.lean','unit_defect_add_guard admissible_domain forced_refusal amplitude_floor nonzero_winding_forces_defect','Unitary relator defect/branch-guard budget and winding floor under the branch hypotheses; not a general physical calibration.')
ext([30,74],'upg-lean','UPGDiracRefraction.lean','refraction_law refraction_equal_potentials turning_barrier regularized_refraction','Conditional scalar refraction/turning algebra from conserved quantities; the Lagrangian origin is supplied separately.')
ext([155],'three-body-lean','ThreeBody/Basic.lean','dPhi_theta₁ dPhi_theta₂ dPhi_phi₁ dPhi_phi₂ gram_eq gram_det_trace syzygy_rank_drop gap_quadratic','Declared shape-sphere differential and Gram spectrum, rank drop and pole-gap asymptotic; not all three-body dynamics.')
ext([42],'square-case-lean','SquareCase/Secular.lean','eigenvalue_secular secular_strict eigenvalues_separated secular_root_in_gap eigenvalue_in_gap','Distinct-pole positive-residue secular equation has exactly one root per consecutive gap under the stated hypotheses; not all non-Hermitian transports.')
ext([43],'square-case-lean','SquareCase/Transport.lean','trace_transport coefficient_forced','Trace-one Gram matrix and nonzero Tr(TH) force coefficient two; the nonzero condition is essential.')
ext([134],'what-transport-keeps-lean','WTK/Transport.lean','gram_selection_step tied_fixed_gram tied_fixed_normalized tied_block_gram','Finite combining inequality and explicit tied-growth examples; the general convergence theorem and identification with a recurrence minimal solution are not formalized here.')
ext([135],'what-transport-keeps-lean','WTK/Transport.lean','pairing_conserved pairing_frame_invariant readout_error','Exact inverse-dual and moving-frame pairing conservation and scalar error bound; not a Hermitian-metric identification.')
ext([148],'what-transport-keeps-lean','WTK/Response.lean','rank_one_stress tensor_overlap stress_composition','Finite rank-one stress/tensor product law; no generic tensor-product spectral-selection theorem.')
ext([149],'what-transport-keeps-lean','WTK/Field.lean','B0_charpoly rail_root rail_roots_product','Exact characteristic polynomial and reciprocal roots for the reconstructed matrix; no new Apéry irrationality or challenge submission proof.')
ext([168],'electron-screening-lean','ElectronScreening/Basic.lean','fit_above_mean fit_below_max','Conditional convex-yield fit bounds (Jensen) under the specified model; measured overshoot and experimental calibration need data.')
ext([116],'coboundary-k3-lean','CoboundaryK3/Basic.lean','delta_prod disp_gram cycle_laplacian_eigen','Permutation displacement Gram and trigonometric identity; cycle eigenvalues and the full projector census are additional identifications.')
ext([146],'coboundary-k3-lean','CoboundaryK3/Basic.lean','witness_k4 witness_k5 witness_k6 witness_k7 witness_k8 gauge_lower gauge_lower_bb search_sound','Exact finite witnesses and sound lower-bound searches for k=4 through 8; not the general all-k equality theorem by itself.')

GUARDS=json.loads(a.guards.read_text())
guardmap=collections.defaultdict(list)
for g in GUARDS:
 for i in g['cards']:guardmap[int(i[1:])].append(g['note'])
guardmap[56].append('The published card repeats the withdrawn nonintersection caption. A curve can meet a point; the current Lean result proves only non-surjectivity of a combined R^2 -> R^3 derivative.')
guardmap[75].append('Ordered denominator signs do not force exact middle cancellation without balanced weights. The independent Euler audit also corrects the sign of lambda squared; see the retained application guard.')
guardmap[90].append('Local line-element speed exponent n/2 differs from integrated distance exponent 1+n/2. Selected normal forms do not classify all closed/open physical systems.')
SOURCE=[]
for f in ZEN['files']:
 if f['key'] in ('atlas_cards_v7_html.zip','operator_first_atlas_continuous_v4.html'):
  SOURCE.append({k:f[k]for k in ('key','checksum','size')})
source_path=OUT/'source_cards.json'
cards=[]
with zipfile.ZipFile(ARCHIVE) as z:
 for i in range(1,208):
  matches=[n for n in z.namelist() if re.search(r'(?:^|/)html/B'+str(i)+r'\.html$',n)]
  assert len(matches)==1,(i,matches)
  raw=z.read(matches[0]);p=DOM();p.feed(raw.decode());n=p.root
  refs=MAP.get(i,[])
  status='local_kernel_mapped' if any(x['repository']==L for x in refs) else 'external_kernel_mapped' if refs else 'not_mapped_in_audited_scope'
  grade=get(n,'bgrade');legs={}
  for leg in n.all('leg'):
   label=get(leg,'k');ps=[c for c in leg.children if isinstance(c,Node)and c.tag=='p']
   if label and ps:legs[label]=ps[0].text()
  title=re.search(r'<title>([\s\S]*?)</title>',raw.decode()).group(1)
  title=html.unescape(title)
  row=dict(id=f'B{i}',title=title,source_grade=grade,source_file=matches[0],source_sha256=hashlib.sha256(raw).hexdigest(),source_url=f'https://zenodo.org/records/23590925/files/atlas_cards_v7_html.zip?download=1',claim=get(n,'beq'),explanation=get(n,'bsay'),assumptions=legs,closed_when=get(n,'closed'),source_reference=get(n,'ref'),coverage_status=status,full_card_certified=False,proof_references=refs,audit_notes=guardmap[i],next_obligation=('Check all remaining headline, geometric, analytic and physical clauses against the exact mapped theorem statements; formalize any missing clauses.' if refs else 'Formalize the displayed claim under the card Carry/Check hypotheses or locate and audit an existing formalization; preserve the source grade until then.'),witness_status='Published card witness only; no fresh numerical replay is claimed by this ledger.')
  # The class is 'equation' in some source editions; preserve the displayed claim from the original text when needed.
  if not row['claim']:
   for cl in ['eq','equation','bmath','formula']:
    row['claim']=get(n,cl)
    if row['claim']:break
  cards.append(row)
external=json.loads((OUT/'external_sources.json').read_text())
for c in cards:
 for ref in c['proof_references']:
  if ref['repository']==L:
   ref.update(commit='172175e410ce7cbbf277c84d95e5d625d8cf7586',snapshot_path=ref['path'])
  else:
   e=next(e for e in external if e['repo']==ref['repository']and e['path']==ref['path']);ref.update(commit=e['head'],snapshot_path=e['snapshot_path'])
  ref['url']=f"https://github.com/{ref['repository']}/blob/{ref['commit']}/{ref['path']}"
metadata=dict(schema_version=1,author='Jeromie Beasley',audited_date='2026-10-23',publication_doi='10.5281/zenodo.23590925',publication_url='https://doi.org/10.5281/zenodo.23590925',publication_title=ZEN['metadata']['title'],concept_doi=ZEN.get('conceptdoi'),source_files=SOURCE,source_archive_sha256=hashlib.sha256(ARCHIVE.read_bytes()).hexdigest(),audit_scope='The 37 local declarations and explicitly listed kernels in sixteen external repositories. Not a search of every repository or Mathlib theorem. A missing mapping is an open audit item, not proof of absence.',cards=cards)
OUT.mkdir(parents=True,exist_ok=True)
(OUT/'coverage.json').write_text(json.dumps(metadata,ensure_ascii=False,indent=2)+'\n')
(OUT/'publication.json').write_text(json.dumps({k:v for k,v in metadata.items()if k!='cards'},ensure_ascii=False,indent=2)+'\n')
count=collections.Counter(c['coverage_status']for c in cards);grades=collections.Counter(c['source_grade']for c in cards)
lines=['# 207-card Lean coverage ledger','', 'Jeromie Beasley · audit dated 23 October 2026','',f"Published source: [{metadata['publication_title']}]({metadata['publication_url']}). The archive and continuous HTML match the Zenodo checksums exactly.",'', 'This ledger records evidence for every card B1–B207. A source grade of THEOREM is not itself a Lean certificate. A mapped kernel proves only the linked Lean declaration under its written hypotheses; no complete-card certification is assigned by this audit. Missing mappings mean not yet mapped in the audited scope, not that no proof exists anywhere.','', '## Coverage summary','',f"- {count['local_kernel_mapped']} cards have mapped kernels in this repository (37 declarations, with overlap).",f"- {count['external_kernel_mapped']} further cards have mapped kernels in the sixteen inspected companion repositories.",f"- {count['not_mapped_in_audited_scope']} cards still need a formal-proof mapping in this audit.",'- The published 207-card files are kept separate from the historical 93-card directory; neither edition is overwritten.','- Historical CI evidence is pinned below; a fresh PR build checks the local Lean modules and coverage validator. External snapshot files are evidence, not imports into this project build.','', '## Exact evidence and limits','', 'The local baseline is commit `172175e410ce7cbbf277c84d95e5d625d8cf7586`. Its [successful proof check](https://github.com/dicipler-pixel/relational-atlas-lean/actions/runs/38548449492) ran the build, independent kernel replay, axiom audit and seven false controls. This is historical evidence, not a new run. The current PR run is the source for fresh checks.','', 'The connection-energy repository has a committed verification report, not a GitHub Actions run. Its report records a clean build, five module kernel replays, 49 audited declarations and five rejected false controls. This ledger retains that evidence and source hashes but does not claim to have rebuilt that external project.','', 'Cross-repository theorem snapshots and pinned commits are listed in [external_sources.json](external_sources.json). Per-card assumptions, source hashes, exact scopes and remaining obligations are in [coverage.json](coverage.json). The validator checks that all 207 IDs occur once, proof names exist in the pinned snapshots and all 37 local declarations are represented in the inventory. It does not mathematically prove the mapping from prose to Lean.','', '## Corrections that must remain visible','', 'B56: the published nonintersection caption exceeds the proved rank obstruction. B75: opposite signs alone do not ensure exact cancellation, and the spinning-key sign correction remains necessary. B90: local speed and integrated distance have different exponents; selected normal forms are not a universal openness test. Further retained guards cover B23, B77, B91, B156, B169 and B196. Source text is preserved, not silently repaired.','', '## All 207 cards','', '| Card | Published claim | Source grade | Lean coverage | Exact proved scope / remaining limit |','| --- | --- | --- | --- | --- |']
for c in cards:
 refs=c['proof_references'];scope='; '.join(r['scope']for r in refs)if refs else c['next_obligation']
 if c['audit_notes']:scope+=' AUDIT: '+' '.join(c['audit_notes'])
 proof='; '.join(f"[{', '.join(r['declarations'])}]({r['url']})"for r in refs)or 'Not mapped in audited scope'
 title=c['title'].split(' — ',1)[-1]
 clean=lambda s:s.replace('|','\\|').replace('\n',' ')
 lines.append('| '+' | '.join(map(clean,[c['id'],title,c['source_grade'],proof,scope]))+' |')
(OUT/'README.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(dict(cards=len(cards),coverage=dict(count),source_grades=dict(grades),claims_missing=[c['id']for c in cards if not c['claim']]),indent=2))
