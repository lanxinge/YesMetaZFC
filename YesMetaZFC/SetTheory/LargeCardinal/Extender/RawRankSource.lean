import YesMetaZFC.SetTheory.LargeCardinal.Extender.LocalFormula
import YesMetaZFC.SetTheory.LargeCardinal.Extender.StrengthRank
import YesMetaZFC.Model.SetTheory.Internal.FiniteSpaceBounded
import YesMetaZFC.SetTheory.LargeCardinal.Extender.StrengthAgreement
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.RelativeRankEnumeration
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.SetTheory.LargeCardinal.Extender.CriticalPoint
import YesMetaZFC.SetTheory.LargeCardinal.Extender.BoundedIdentity
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.InitialPull
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.StepSyntax
import YesMetaZFC.Model.SetTheory.Reflection.ZfcTransfer
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawAlphabet
import YesMetaZFC.SetTheory.LargeCardinal.Extender.LevelTransfer
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawPresent
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawColimit
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawApplication
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CriticalBound
import YesMetaZFC.SetTheory.LargeCardinal.Game.Basis
import YesMetaZFC.SetTheory.CumulativeComparison
import YesMetaZFC.Model.SetTheory.Relations.OmegaCut
import YesMetaZFC.Model.SetTheory.Relations.OmegaEvaluation
import YesMetaZFC.Model.SetTheory.Relations.NativeRank
import YesMetaZFC.Model.SetTheory.Relations.LayerSeparation
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.Model.SetTheory.Relations.NativeSmemSlice

/-! # 短扩展器、不可达支撑与最大强度的单一有界公式

所需有限列空间由公式量化并完整识别。最大强度仍由同一张扩展器的
原有界超幂和缺失子集判定；没有外部提供的强度值表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def ex_strength_m {d} (ω κ L X F : Term d) : Formula 1 d := set[d] ⟪
  ⌜L⌝ₛ ∈ ⌜X⌝ₛ ∧ (∃ K ∈ ⌜X⌝ₛ, ∃ H ∈ ⌜X⌝ₛ,
    ⌜fs_space0_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, ⌜κ⌝ₛ, K) ∧ ⌜fs_space0_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, ⌜L⌝ₛ, H) ∧
    ⌜ex_strength0_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜X⌝ₛ, ⌜F⌝ₛ, K, H))⟫
derive_free_closed ex_strength_m

theorem ex_strength_delta_l {d} (ω κ L X F : Term d) : (ex_strength_m ω κ L X F).IsDelta0 :=
  .conj (.mem ..) (.existsMem _ (.existsMem _ (.conj (fs_space0_delta_l ..)
    (.conj (fs_space0_delta_l ..) (ex_strength0_delta_l ..)))))

def ex_quality_m {d} (ω κ L X F : Term d) : Formula 1 d :=
  .conj (ex_local_m ω κ L X F) (.conj (ex_inaccessible_m ω X L) (ex_strength_m ω κ L X F))
derive_free_closed ex_quality_m

theorem ex_quality_delta_l {d} (ω κ L X F : Term d) : (ex_quality_m ω κ L X F).IsDelta0 :=
  .conj (ex_local_delta_l ..) (.conj (ex_inaccessible_delta_l ..) (ex_strength_delta_l ..))

variable (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

theorem ex_strength_sat_l {d K₀ R} (ρ : Env M d) (ω κ L X F : Term d)
    (source : Ep_source_d (kp_pair_l hKP) (ω.eval ρ) (κ.eval ρ) K₀ (X.eval ρ) R) :
    Formula.satisfies ρ (ex_strength_m ω κ L X F) ↔
      Ex_strength_d (kp_pair_l hKP) (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (F.eval ρ) := by
  let w (a : Term d) := a.weaken.weaken
  have sk K H : Formula.satisfies ((ρ.push K).push H)
      (fs_space0_m (w ω) (w X) (w κ) Term.newest.weaken) ↔ K = K₀ := by
    simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      fs_space0_iff_l hKP (K₀ := K₀) ((ρ.push K).push H) (w ω) (w X) (w κ) Term.newest.weaken
        (by simpa only [w, Definitional.Term.eval_weaken] using (source.finite_l hKP))
        (by simpa only [w, Definitional.Term.eval_weaken, Structure.MemberSubset] using source.transitive K₀ source.finite.mem_l)
  have sl K H H₀ (seq : Fseq_space_d I (ω.eval ρ) (L.eval ρ) H₀) (hH : M.mem H₀ (X.eval ρ)) :
      Formula.satisfies ((ρ.push K).push H) (fs_space0_m (w ω) (w X) (w L) .newest) ↔ H = H₀ := by
    simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      fs_space0_iff_l hKP (K₀ := H₀) ((ρ.push K).push H) (w ω) (w X) (w L) .newest
        (by simpa only [w, Definitional.Term.eval_weaken] using seq)
        (by simpa only [w, Definitional.Term.eval_weaken, Structure.MemberSubset] using source.transitive H₀ hH)
  have core H (seq : Fseq_space_d I (ω.eval ρ) (L.eval ρ) H) :
      Formula.satisfies ((ρ.push K₀).push H) (ex_strength0_m (w ω) (w κ) (w L) (w X) (w F) Term.newest.weaken .newest) ↔
      Ex_strength_d (kp_pair_l hKP) (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (F.eval ρ) := by
    simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      ex_strength0_sat_l hKP ((ρ.push K₀).push H) (w ω) (w κ) (w L) (w X) (w F) Term.newest.weaken .newest
        (by simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using (source.finite_l hKP))
        (by simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using seq)
  dsimp only [w] at sk sl core
  simp only [ex_strength_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_existsMem_iff, sk, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨hL, K, _, H, _, eqK, space, matrix⟩
    subst K
    obtain ⟨H₀, hH₀, seq⟩ := (source.sequences_l hKP).1 (L.eval ρ) hL
    have eqH := (sl K₀ H H₀ seq hH₀).mp space
    subst H
    exact (core H₀ seq).mp matrix
  · intro strength
    have hL := strength.2.2.1
    obtain ⟨H, hH, seq⟩ := (source.sequences_l hKP).1 (L.eval ρ) hL
    exact ⟨hL, K₀, source.finite.mem_l, H, hH, rfl, (sl K₀ H H seq hH).mpr rfl, (core H seq).mpr strength⟩

theorem ex_quality_sat_l {d K R} (ρ : Env M d) (ω κ L X F : Term d)
    (source : Ep_source_d (kp_pair_l hKP) (ω.eval ρ) (κ.eval ρ) K (X.eval ρ) R) :
    Formula.satisfies ρ (ex_quality_m ω κ L X F) ↔
      It_local_d I (ω.eval ρ) (X.eval ρ) R (κ.eval ρ) (L.eval ρ) (F.eval ρ) ∧
      Sc_inaccessible_d (ω.eval ρ) (X.eval ρ) (L.eval ρ) ∧
      Ex_strength_d (kp_pair_l hKP) (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (F.eval ρ) :=
  (Formula.satisfies_conj_iff ..).trans (and_congr (ex_local_sat_l I ρ ω κ L X F source.transitive source.code)
    ((Formula.satisfies_conj_iff ..).trans (and_congr (ex_inaccessible_sat_l ρ ω X L source.transitive)
      (ex_strength_sat_l hKP ρ ω κ L X F source))))

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原一步证书内的共同秩段与有界池

反向子集包含直接来自原秩源的子集闭包，故最大强度给出同一支撑秩段。
再用原一步超幂构造较大容器的同一有界池，保留其中的秩历史和实际小性。
本模块可解释在所属原关系模型内部；它不对外部迭代模型断言良基性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一原池的常值像、低秩固定及恒等节点的支撑值。 -/
structure Eo_image_d (J : kpair_convention_l.Interpretation M) (ω κ L X F j B W A e : M.Domain) : Prop where
  member : M.mem B W
  constants : ∀ x y, M.mem x B → (Eb_const_d X B A e x y ↔ Rd_entry_d x y j)
  numbers : Rd_entry_d ω ω j ∧ ∀ n, M.mem n ω → Rd_entry_d n n j
  fixed : ∃ P, V_d J κ P ∧ M.mem P B ∧
    (Ec_source_d J ω κ L X F → Ea_atoms_d ω κ L F → En_source_d ω κ L X F →
      Ep_positive_d ω κ X F → ∀ x, M.mem x P → Rd_entry_d x x j)
  coordinates : Ec_source_d J ω κ L X F → Ea_atoms_d ω κ L F → En_source_d ω κ L X F →
    ∀ u a f, M.mem u A → KPair_d M u a f → (∀ s x, Rd_entry_d s x f → s = x) → Rd_entry_d u a e

include hZF in
private theorem er_ordinal_bound_mem_l {L θ Y : M.Domain} (hl : M.IsOrdinal L) (ht : M.IsOrdinal θ)
    (le : M.MemberSubset L θ) (trans : M.TransitiveSet Y) (hθ : M.mem θ Y) : M.mem L Y := by
  rcases hl.trichotomy hZF.1 ht (KP.difference_exists_d (ZF.modelsKP hZF))
    (KP.intersection_exists_d (ZF.modelsKP hZF) L θ) with eq | lt | gt
  · exact (hZF.1.eq_of_same_members L θ eq).symm ▸ hθ
  · exact trans θ hθ L lt
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) θ (le θ gt)).elim

variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "Jp" => kp_pair_l (ZF.modelsKP hZ)

theorem It_ultra_d.strength_rank_l {ω κ K L X R F δ c d N S j θ : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZ)) ω κ K X R) (rank : V_d Jp δ X) (height : M.IsLimitOrdinal δ)
    (family : Em_source_d ω κ L X F) (hm : Smem_d Jp c X R) (hn : Smem_d Jp d N S)
    (card : Sc_inaccessible_d ω X L) (strength : Ex_strength_d (kp_pair_l (ZF.modelsKP hZ)) ω κ L X F)
    (ord : M.IsOrdinal κ) (hκθ : Rd_entry_d κ θ j) (bound : M.MemberSubset L θ)
    (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZ)) ω κ L F c d j) :
    ∃ W K₀ K₁, V_d Jp L W ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZ)) ω L K₀ X R ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZ)) ω L K₁ N S ∧
      Er_level_d X L W ∧ M.mem W N ∧ Vr_d N L W ∧ Sc_rank_size_d Jp N L ∧
      ∀ μ, M.mem μ L → Ea_agree_d ω μ X N := by
  have nt := ultra.transitive_l hZ hn.1
  have hj := ultra.elementary_l hZ hm.1 hn.1
  obtain ⟨above, regular, strong⟩ := sc_v_inaccessible_up_l (ZF.modelsKP hZ) height rank card
  have hLX := strength.2.2.1
  have hLN := er_ordinal_bound_mem_l hZ regular.isCardinal.1
    (hj.ordinal_l hZ source.omega source.transitive nt hm hn hκθ ord) bound nt
    (hj.1.1.output_mem_of_pairMember hκθ)
  have theory := source.theory.map_l Jp hZ source.omega hm.1 hn.1 hj
  have below := regular.isCardinal.1.transitive ω above
  obtain ⟨K₀, sx⟩ := source.rebase_l hLX below
    (sc_ordinal_small_l hZ source.omega source.transitive hm source.theory hLX regular.isCardinal.1)
  obtain ⟨K₁, sy⟩ := source.successor_l hZ hm hn nt hj hLN below
    (sc_ordinal_small_l hZ source.omega nt hn theory hLN regular.isCardinal.1)
  have es := strength.realize_l hZ source family hm hn ultra ord.transitive hκθ bound
  have back : Ea_subset_d ω L N X := fun n D A hn ds sub _ =>
    v_subset_mem_l Jp rank (sx.space_mem_l hZ hn ds) sub
  have same := es.agree_l hZ sx sy regular.isCardinal.1 above back
  have sizes := sc_v_rank_size_l hZFC source.omega height rank card
  obtain ⟨W, hw⟩ := ZF.v_exists_l Jp hZ regular.isCardinal.1
  have level := ep_relative_rank_l hZFC source rank height
    (ZF.v_ordinal_height_l hZ rank regular.isCardinal.1 hLX) above regular strong hw
  have hierarchy := (sc_hierarchy_iff_l hZ source.omega source.transitive nt hm hn hj).mp
    (sc_v_hierarchy_l hZ height rank)
  obtain ⟨W', hW', hw'⟩ := hierarchy L hLN regular.isCardinal.1
  have eq := ea_rank_agree_l hZ sx sy regular.isLimitOrdinal above sizes same level.member level.hierarchy hW' hw'
  subst W'
  have power := (sc_power_iff_l hZ source.omega source.transitive nt hm hn hj).mp (sc_v_power_l (ZF.modelsKP hZ) height rank)
  have sizes' := ea_rank_size_l hZ sy power hierarchy source.transitive regular.isLimitOrdinal
    hW' level.member hw' level.hierarchy sizes
  exact ⟨W, K₀, K₁, hw, sx, sy, level, hW', hw', sizes', same⟩

/-- 原有界池的像中包含整个支撑秩段；秩历史与编号都属于同一容器。 -/
theorem It_ultra_d.owned_rank_l {ω κ K L X R F δ c d N S j θ α B : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZ)) ω κ K X R) (rank : V_d Jp δ X) (height : M.IsLimitOrdinal δ)
    (family : Em_source_d ω κ L X F) (hm : Smem_d Jp c X R) (hn : Smem_d Jp d N S)
    (card : Sc_inaccessible_d ω X L) (strength : Ex_strength_d (kp_pair_l (ZF.modelsKP hZ)) ω κ L X F)
    (ord : M.IsOrdinal κ) (hκθ : Rd_entry_d κ θ j) (bound : M.MemberSubset L θ)
    (hαL : M.mem α L) (hα : M.IsLimitOrdinal α) (rankB : V_d Jp α B) (hκB : M.mem κ B)
    (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZ)) ω κ L F c d j) :
    ∃ W Y A Q e, V_d Jp L W ∧ Er_level_d X L W ∧ M.mem W N ∧ Vr_d N L W ∧
      Eb_collapse_d ω κ L K X B F A Q Y e ∧
      M.mem Y X ∧ M.mem L Y ∧ M.mem W Y ∧ Vr_d Y L W ∧ Sc_rank_size_d Jp Y L ∧ Sc_small_d Y W ∧
      Eo_image_d Jp ω κ L X F j B W A e ∧ Es_strength_d X L Y := by
  obtain ⟨W, _, _, hw, _, target, level, hWN, rankWN, sizes, _⟩ :=
    ultra.strength_rank_l hZFC source rank height family hm hn card strength ord hκθ bound
  have nt := ultra.transitive_l hZ hn.1
  have hj := ultra.elementary_l hZ hm.1 hn.1
  have transB := v_transitive_l Jp rankB
  have hBW := ZF.v_mem_l Jp hZ rankB hw hαL
  have hBX := source.transitive W level.member B hBW
  have hαX := source.transitive L strength.2.2.1 α hαL
  have hαδ := ZF.v_ordinal_height_l hZ rank hα.1 hαX
  obtain ⟨D, f, hD, hf, history, _⟩ := vr_source_l hZ rank height hαδ rankB
  have relativeB : Vr_d X α B := ⟨D, f, hD, hf, fun x _ => history x⟩
  obtain ⟨Y, hYN, hBY⟩ := hj.1.1.2.2 B hBX
  obtain ⟨a, _, hαa⟩ := hj.1.1.2.2 α hαX
  have rankY := (hj.hierarchy_l hZ source.omega source.transitive nt hm hn hαa hBY).mp relativeB
  have limitY := (hj.limit_l hZ source.omega source.transitive nt hm hn hαa).mp hα
  have yt := rankY.transitive_l nt hYN
  have hθY := (hj.member_l Jp hZ source.omega hm hn hκθ hBY).mp hκB
  have hl := (sc_v_inaccessible_up_l (ZF.modelsKP hZ) height rank card).2.1.isLimitOrdinal
  have hLY := er_ordinal_bound_mem_l hZ hl.1
    (hj.ordinal_l hZ source.omega source.transitive nt hm hn hκθ ord) bound yt hθY
  obtain ⟨hWY, rankWY⟩ := rankY.rank_l hZ nt hYN limitY hLY hWN rankWN
  have sizesY := sizes.rank_l hZ nt hYN rankY limitY hLY
  obtain ⟨hYX, A, Q, e, owned⟩ := it_ultra_owned_image_l hZ source (sc_v_power_l (ZF.modelsKP hZ) height rank)
    family hm hn ultra strength.2.2.1 strength.2.2.2.1 hl level
      (v_transitive_l Jp hw B hBW κ hκB) hBW transB hBY
  obtain ⟨cY, RY, codeY⟩ := smdl_membership_l Jp hZ ⟨L, hLY⟩
  have theoryY := target.rank_theory_l hZ hYN rankY limitY codeY
  obtain ⟨W', g, hW', rankW', hg, bij⟩ := sizesY.level
  have eq := rankW'.unique_l hZ yt hW' hWY rankWY
  subst W'
  have small := sc_small_image_l hZ source.omega yt codeY theoryY hLY hWY hg
    ((rf_small_mem_l Jp (ZF.modelsKP hZ) yt codeY hLY).mp (sc_ordinal_small_l hZ source.omega yt codeY theoryY hLY hl.1))
      (fn0_of_function_l (ZF.modelsKP hZ) bij.1.1) bij.2
  -- 低秩固定在原所属模型内证明；反射后只读取同一个 P 和原常值图。
  have hκα := ZF.v_ordinal_height_l hZ rankB ord hκB
  have hκL := hl.1.transitive α hαL κ hκα
  obtain ⟨P, rankP⟩ := ZF.v_exists_l Jp hZ ord
  have hPB := ZF.v_mem_l Jp hZ rankP rankB hκα
  have hPW := v_transitive_l Jp hw B hBW P hPB
  obtain ⟨C, G, hC, hG, cert, _⟩ := vr_source_l hZ hw hl hκL rankP
  have inner : Vr_d W κ P := ⟨C, G, hC, hG, fun x _ => cert x⟩
  have px := level.hierarchy.of_rank_l source.transitive level.member hPW inner
  have pn := rankWN.of_rank_l nt hWN hPW inner
  have image : Eo_image_d Jp ω κ L X F j B W A e := by
    refine ⟨hBW, (owned.image_l hZ source family hm hn ultra hBX transB).2,
      ⟨hj.omega_l Jp hZ source.omega source.transitive nt hm hn source.omega_mem,
        hj.natural_l hZ source.omega source.transitive nt hm hn source.omega_mem⟩, ⟨P, rankP, hPB, ?_⟩, ?_⟩
    · intro coherent atoms normal principal
      have critical := ultra.critical_source_l hZ source family coherent atoms normal ord hl.1 principal hκL hm hn hκθ
      exact hj.rank_fixed_l hZ source.omega source.transitive nt hm hn hκθ critical.fixed
        (source.transitive W level.member P hPW) px (nt W hWN P hPW) pn
    · intro coherent atoms normal u a f hu pair id
      exact owned.identity_l hZFC source family coherent atoms normal ord.transitive hl.1.transitive
        hm hn ultra hBX transB hu pair id
  -- 同一有界像包含支撑以下的全部子集；原超幂缺失的子集也不可能落入它。
  have es := strength.realize_l hZ source family hm hn ultra ord.transitive hκθ bound
  have exactness : Es_strength_d X L Y := by
    refine ⟨fun μ hμ x _ sub => yt W hWY x
      (v_subset_mem_l Jp hw (ZF.v_ordinal_mem_l Jp hZ hw hμ) sub), ?_⟩
    obtain ⟨x, hx, sub, missing⟩ := es.2
    exact ⟨x, hx, sub, fun hy => missing (nt Y hYN x hy)⟩
  exact ⟨W, Y, A, Q, e, hw, level, hWN, rankWN, owned, hYX, hLY, hWY, rankWY, sizesY, small, image, exactness⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原共同秩段构造的有限全称规则

规则保留同一扩展器、实际超幂边和原有界池，结论包括完整秩历史、小性和
新共同层的实际 ZFC 证书及总关系的层内见证界。常值像、低秩固定和恒等节点值先在原模型内证明，
再作为同一有限结论回读；反射结构只用 KP。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

private def eo_level_m {d} (X L W : Term d) : Formula 1 d := set[d] ⟪
  ⌜W⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜pn_rank_m⌝ₚ(⌜X⌝ₛ, ⌜L⌝ₛ, ⌜W⌝ₛ) ∧
    (∃ T ∈ ⌜X⌝ₛ, ∃ f ∈ ⌜X⌝ₛ, ⌜wc_iso_m⌝ₚ(⌜L⌝ₛ, T, ⌜W⌝ₛ, f))⟫
derive_free_closed eo_level_m

private theorem eo_level_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (X L W : Term d) :
    Formula.satisfies ρ (eo_level_m X L W) ↔ Er_level_d (X.eval ρ) (L.eval ρ) (W.eval ρ) := by
  simp only [eo_level_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    pn_rank_sat_l hKP, Formula.satisfies_existsMem_iff, wc_iso_sat_l hKP.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨m, r, T, hT, f, hf, i⟩ => ⟨m, r, T, f, hT, hf, i⟩,
    fun ⟨m, r, T, f, hT, hf, i⟩ => ⟨m, r, T, hT, f, hf, i⟩⟩

private def eo_sizes_m {d} (Y L : Term d) : Formula 1 d := set[d] ⟪
  (∃ W ∈ ⌜Y⌝ₛ, ∃ f ∈ ⌜Y⌝ₛ, ⌜pn_rank_m⌝ₚ(⌜Y⌝ₛ, ⌜L⌝ₛ, W) ∧
    ⌜Formula.isBijectionFromTo kpair_convention_l⌝ₚ(f, ⌜L⌝ₛ, W)) ∧
  (∀ α ∈ ⌜L⌝ₛ, ∃ W ∈ ⌜Y⌝ₛ, ∃ μ ∈ ⌜L⌝ₛ, ∃ f ∈ ⌜Y⌝ₛ,
    ⌜pn_rank_m⌝ₚ(⌜Y⌝ₛ, α, W) ∧ ⌜Formula.isBijectionFromTo kpair_convention_l⌝ₚ(f, μ, W))⟫
derive_free_closed eo_sizes_m

private theorem eo_sizes_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (Y L : Term d) :
    Formula.satisfies ρ (eo_sizes_m Y L) ↔ Sc_rank_size_d (kp_pair_l hKP) (Y.eval ρ) (L.eval ρ) := by
  simp only [eo_sizes_m, Formula.satisfies_conj_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_forallMem_iff, pn_rank_sat_l hKP,
    Formula.satisfies_isBijectionFromTo_iff (kp_pair_l hKP) hKP.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨⟨W, hW, f, hf, r, b⟩, l⟩ => ⟨⟨W, f, hW, r, hf, b⟩,
    fun α hα => (l α hα).elim fun W ⟨hW, μ, hμ, f, hf, r, b⟩ => ⟨W, μ, f, hW, r, hμ, hf, b⟩⟩,
    fun ⟨⟨W, f, hW, r, hf, b⟩, l⟩ => ⟨⟨W, hW, f, hf, r, b⟩,
      fun α hα => (l α hα).elim fun W ⟨μ, f, hW, r, hμ, hf, b⟩ => ⟨W, hW, μ, hμ, f, hf, r, b⟩⟩⟩

def eo_image_m {d} (ω κ L X F j B W A e : Term d) : Formula 1 d := set[d] ⟪
  ⌜B⌝ₛ ∈ ⌜W⌝ₛ ∧
  (∀ x y, x ∈ ⌜B⌝ₛ → (⌜eb_const_m⌝ₚ(⌜X⌝ₛ, ⌜B⌝ₛ, ⌜A⌝ₛ, ⌜e⌝ₛ, x, y) ↔ ⌜rd_entry0_m⌝ₚ(x, y, ⌜j⌝ₛ))) ∧
  (⌜rd_entry0_m⌝ₚ(⌜ω⌝ₛ, ⌜ω⌝ₛ, ⌜j⌝ₛ) ∧ (∀ n ∈ ⌜ω⌝ₛ, ⌜rd_entry0_m⌝ₚ(n, n, ⌜j⌝ₛ))) ∧
  (∃ P, ⌜v_sigma_m⌝ₚ(⌜κ⌝ₛ, P) ∧ P ∈ ⌜B⌝ₛ ∧
    (⌜ec_source_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜X⌝ₛ, ⌜F⌝ₛ) → ⌜ea_atoms_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜F⌝ₛ) →
      ⌜en_source_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜X⌝ₛ, ⌜F⌝ₛ) → ⌜ep_positive_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜X⌝ₛ, ⌜F⌝ₛ) →
      ∀ x ∈ P, ⌜rd_entry0_m⌝ₚ(x, x, ⌜j⌝ₛ))) ∧
  (⌜ec_source_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜X⌝ₛ, ⌜F⌝ₛ) → ⌜ea_atoms_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜F⌝ₛ) →
    ⌜en_source_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜X⌝ₛ, ⌜F⌝ₛ) →
    ∀ u a f, u ∈ ⌜A⌝ₛ → ⌜kpair0_m⌝ₚ(u, a, f) → (∀ s x, ⌜rd_entry0_m⌝ₚ(s, x, f) → s = x) →
      ⌜rd_entry0_m⌝ₚ(u, a, ⌜e⌝ₛ))⟫
derive_free_closed eo_image_m

theorem eo_image_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω κ L X F j B W A e : Term d) :
    Formula.satisfies ρ (eo_image_m ω κ L X F j B W A e) ↔
      Eo_image_d (kp_pair_l hKP) (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (F.eval ρ)
        (j.eval ρ) (B.eval ρ) (W.eval ρ) (A.eval ρ) (e.eval ρ) := by
  simp only [eo_image_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff,
    eb_const_sat_l hKP.1, rd_entry0_sat_l hKP.1, Formula.satisfies_exists_iff, v_sigma_sat_l hKP,
    ec_source_sat_l (kp_pair_l hKP) hKP.1, ea_atoms_sat_l hKP.1, en_source_sat_l hKP.1,
    ep_positive_sat_l hKP.1, Formula.satisfies_forallMem_iff, kpair0_sat_l hKP.1,
    Formula.satisfies_extensionalEq_iff_eq hKP.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨m, c, n, f, v⟩ => ⟨m, c, n, f, v⟩,
    fun h => ⟨h.member, h.constants, h.numbers, h.fixed, h.coordinates⟩⟩

private def eo_owned_m {d} (ω κ K L X F j N B H W Y A Q e : Term d) : Formula 1 d := set[d] ⟪
  ⌜v_sigma_m⌝ₚ(⌜L⌝ₛ, ⌜W⌝ₛ) ∧ ⌜eo_level_m⌝ₚ(⌜X⌝ₛ, ⌜L⌝ₛ, ⌜W⌝ₛ) ∧
  ⌜W⌝ₛ ∈ ⌜N⌝ₛ ∧ ⌜pn_rank_m⌝ₚ(⌜N⌝ₛ, ⌜L⌝ₛ, ⌜W⌝ₛ) ∧
  ⌜eb_collapse_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜K⌝ₛ, ⌜X⌝ₛ, ⌜B⌝ₛ, ⌜F⌝ₛ, ⌜A⌝ₛ, ⌜Q⌝ₛ, ⌜Y⌝ₛ, ⌜e⌝ₛ, ⌜H⌝ₛ) ∧
  ⌜Y⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜L⌝ₛ ∈ ⌜Y⌝ₛ ∧ ⌜W⌝ₛ ∈ ⌜Y⌝ₛ ∧ ⌜pn_rank_m⌝ₚ(⌜Y⌝ₛ, ⌜L⌝ₛ, ⌜W⌝ₛ) ∧
  ⌜eo_sizes_m⌝ₚ(⌜Y⌝ₛ, ⌜L⌝ₛ) ∧ ⌜sc_small0_m⌝ₚ(⌜Y⌝ₛ, ⌜W⌝ₛ) ∧
  ⌜eo_image_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜X⌝ₛ, ⌜F⌝ₛ, ⌜j⌝ₛ, ⌜B⌝ₛ, ⌜W⌝ₛ, ⌜A⌝ₛ, ⌜e⌝ₛ) ∧
  ⌜es_strength0_m⌝ₚ(⌜X⌝ₛ, ⌜L⌝ₛ, ⌜Y⌝ₛ) ∧
  ⌜sc_bound_m⌝ₚ(⌜W⌝ₛ) ∧
  (∃ c R, ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, ⌜W⌝ₛ, R) ∧ ⌜zc_model_m⌝ₚ(⌜ω⌝ₛ, c, ⌜W⌝ₛ, R))⟫
derive_free_closed eo_owned_m

private theorem eo_owned_sat_l (hKP : M.Models KP) {d} (ρ : Env M d)
    (ω κ K L X F j N B H W Y A Q e : Term d)
    (seq : Fseq_space_d (kp_pair_l hKP) (ω.eval ρ) (L.eval ρ) (H.eval ρ)) :
    Formula.satisfies ρ (eo_owned_m ω κ K L X F j N B H W Y A Q e) ↔
      V_d (kp_pair_l hKP) (L.eval ρ) (W.eval ρ) ∧ Er_level_d (X.eval ρ) (L.eval ρ) (W.eval ρ) ∧
      M.mem (W.eval ρ) (N.eval ρ) ∧ Vr_d (N.eval ρ) (L.eval ρ) (W.eval ρ) ∧
      Eb_collapse_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (K.eval ρ) (X.eval ρ) (B.eval ρ) (F.eval ρ)
        (A.eval ρ) (Q.eval ρ) (Y.eval ρ) (e.eval ρ) ∧
      M.mem (Y.eval ρ) (X.eval ρ) ∧ M.mem (L.eval ρ) (Y.eval ρ) ∧ M.mem (W.eval ρ) (Y.eval ρ) ∧
      Vr_d (Y.eval ρ) (L.eval ρ) (W.eval ρ) ∧ Sc_rank_size_d (kp_pair_l hKP) (Y.eval ρ) (L.eval ρ) ∧
      Sc_small_d (Y.eval ρ) (W.eval ρ) ∧
      Eo_image_d (kp_pair_l hKP) (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (F.eval ρ)
        (j.eval ρ) (B.eval ρ) (W.eval ρ) (A.eval ρ) (e.eval ρ) ∧
      Es_strength_d (X.eval ρ) (L.eval ρ) (Y.eval ρ) ∧ Sc_bound_d (W.eval ρ) ∧
      ∃ c R, Smem_d (kp_pair_l hKP) c (W.eval ρ) R ∧ Zc_model_d (kp_pair_l hKP) (ω.eval ρ) c (W.eval ρ) R := by
  simp only [eo_owned_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    v_sigma_sat_l hKP, eo_level_sat_l hKP, pn_rank_sat_l hKP,
    eb_collapse_sat_l hKP ρ ω κ L K X B F A Q Y e H seq, eo_sizes_sat_l hKP, sc_small0_sat_l hKP, eo_image_sat_l hKP,
    es_strength0_sat_l, sc_bound_sat_l hKP.1,
    Formula.satisfies_exists_iff, smem_sat_l (kp_pair_l hKP), zc_model_sat_l (kp_pair_l hKP) hKP.1,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

-- ω,κ,K,L,X,R,F,δ,c,d,N,S,j,θ,α,B；量词覆盖结构中的全部新参数。
def eo_seed0_m : Formula 1 16 :=
  let p : Fin 16 → Term 16 := Term.bound
  set[16] ⟪⌜ep_source_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 2⌝ₛ, ⌜p 4⌝ₛ, ⌜p 5⌝ₛ) ∧
    ⌜v_sigma_m⌝ₚ(⌜p 7⌝ₛ, ⌜p 4⌝ₛ) ∧ ⌜Formula.isLimitOrdinal⌝ₚ(⌜p 7⌝ₛ) ∧
    ⌜em_source_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 3⌝ₛ, ⌜p 4⌝ₛ, ⌜p 6⌝ₛ) ∧ ⌜Formula.isOrdinal⌝ₚ(⌜p 1⌝ₛ) ∧
    ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p 8⌝ₛ, ⌜p 4⌝ₛ, ⌜p 5⌝ₛ) ∧
    ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p 9⌝ₛ, ⌜p 10⌝ₛ, ⌜p 11⌝ₛ) ∧
    ⌜ex_inaccessible_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 4⌝ₛ, ⌜p 3⌝ₛ) ∧
    ⌜ex_strength_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 3⌝ₛ, ⌜p 4⌝ₛ, ⌜p 6⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜p 1⌝ₛ, ⌜p 13⌝ₛ, ⌜p 12⌝ₛ) ∧ ⌜p 3⌝ₛ ⊆ ⌜p 13⌝ₛ ∧
    ⌜p 14⌝ₛ ∈ ⌜p 3⌝ₛ ∧ ⌜Formula.isLimitOrdinal⌝ₚ(⌜p 14⌝ₛ) ∧
    ⌜v_sigma_m⌝ₚ(⌜p 14⌝ₛ, ⌜p 15⌝ₛ) ∧ ⌜p 1⌝ₛ ∈ ⌜p 15⌝ₛ ∧
    ⌜it_ultra_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 3⌝ₛ, ⌜p 6⌝ₛ, ⌜p 8⌝ₛ, ⌜p 9⌝ₛ, ⌜p 12⌝ₛ)⟫

def eo_result0_m : Formula 1 16 :=
  let p : Fin 16 → Term 16 := Term.bound
  set[16] ⟪∃ H, ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p 0⌝ₛ, ⌜p 3⌝ₛ, H) ∧
    (∃ W Y A Q e, ⌜eo_owned_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 2⌝ₛ, ⌜p 3⌝ₛ, ⌜p 4⌝ₛ, ⌜p 6⌝ₛ,
      ⌜p 12⌝ₛ, ⌜p 10⌝ₛ, ⌜p 15⌝ₛ, H, W, Y, A, Q, e))⟫

theorem eo_seed0_closed_l : eo_seed0_m.FreeClosed := by
  simp -implicitDefEqProofs [eo_seed0_m, Definitional.Formula.FreeClosed]

theorem eo_result0_closed_l : eo_result0_m.FreeClosed := by
  simp -implicitDefEqProofs [eo_result0_m, Definitional.Formula.FreeClosed]

def eo_kernel_m : Formula 1 0 := Formula.forallClosure 16 (.imp eo_seed0_m eo_result0_m)

theorem eo_kernel_closed_l : eo_kernel_m.FreeClosed :=
  (Definitional.Formula.freeClosed_forallClosure _).mpr ⟨eo_seed0_closed_l, eo_result0_closed_l⟩

private theorem eo_result_sat_l (hKP : M.Models KP) (ρ : Env M 16) :
    Formula.satisfies ρ eo_result0_m ↔
      ∃ H, Fseq_space_d (kp_pair_l hKP) (ρ.bound 0) (ρ.bound 3) H ∧
      ∃ W Y A Q e, V_d (kp_pair_l hKP) (ρ.bound 3) W ∧ Er_level_d (ρ.bound 4) (ρ.bound 3) W ∧
      M.mem W (ρ.bound 10) ∧ Vr_d (ρ.bound 10) (ρ.bound 3) W ∧
      Eb_collapse_d (ρ.bound 0) (ρ.bound 1) (ρ.bound 3) (ρ.bound 2) (ρ.bound 4) (ρ.bound 15) (ρ.bound 6) A Q Y e ∧
      M.mem Y (ρ.bound 4) ∧ M.mem (ρ.bound 3) Y ∧ M.mem W Y ∧ Vr_d Y (ρ.bound 3) W ∧
      Sc_rank_size_d (kp_pair_l hKP) Y (ρ.bound 3) ∧ Sc_small_d Y W ∧
      Eo_image_d (kp_pair_l hKP) (ρ.bound 0) (ρ.bound 1) (ρ.bound 3) (ρ.bound 4) (ρ.bound 6) (ρ.bound 12) (ρ.bound 15) W A e ∧
      Es_strength_d (ρ.bound 4) (ρ.bound 3) Y ∧ Sc_bound_d W ∧
      ∃ c R, Smem_d (kp_pair_l hKP) c W R ∧ Zc_model_d (kp_pair_l hKP) (ρ.bound 0) c W R := by
  simp only [eo_result0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fseq_space_sat_l (kp_pair_l hKP) hKP.1, Definitional.Term.eval_weaken]
  apply exists_congr
  intro H
  apply and_congr_right
  intro seq
  refine exists_congr fun W => exists_congr fun Y => exists_congr fun A =>
    exists_congr fun Q => exists_congr fun e => ?_
  exact eo_owned_sat_l hKP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ seq

theorem eo_kernel_true_l (hZFC : M.Models ZFC) (ε : FreeVarId → M.Domain) :
    Formula.satisfies (⟨Fin.elim0, ε⟩ : Env M 0) eo_kernel_m := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  apply (Formula.satisfies_forallClosure_iff ε _).mpr
  intro p
  rw [Formula.satisfies_imp_iff]
  intro seed
  simp only [eo_seed0_m, Formula.satisfies_conj_iff, ep_source_sat_l (ZF.modelsKP hZF),
    v_sigma_sat_l (ZF.modelsKP hZF), Formula.satisfies_isLimitOrdinal_iff, em_source_sat_l hZF.1, Formula.satisfies_isOrdinal_iff,
    smem_sat_l I, rd_entry0_sat_l hZF.1, Formula.satisfies_subset_iff,
    Formula.satisfies_mem_iff, it_ultra_sat_l I hZF.1] at seed
  obtain ⟨source, rank, height, family, ord, hm, hn, card, strength, image, bound, haL, ha, rankB, hkB, ultra⟩ := seed
  have card := (ex_inaccessible_sat_l _ _ _ _ source.transitive).mp card
  have strength := (ex_strength_sat_l (ZF.modelsKP hZF) _ _ _ _ _ _ source).mp strength
  obtain ⟨W, Y, A, Q, e, result⟩ := ultra.owned_rank_l hZFC source rank height
    family hm hn card strength ord image bound haL ha rankB hkB
  obtain ⟨above, regular, strong⟩ := sc_v_inaccessible_up_l (ZF.modelsKP hZF) height rank card
  obtain ⟨cW, R_W, model, certificate⟩ := zc_inaccessible_l hZFC source.omega above regular strong result.1
  have boundW := sc_v_bound_l hZFC source.omega above regular strong result.1
  obtain ⟨H, _, seq⟩ := (source.sequences_l (ZF.modelsKP hZF)).1 (p 3) strength.2.2.1
  obtain ⟨hw, level, wn, rn, pool, yx, ly, wy, ry, sizes, small, images, exactness⟩ := result
  exact (eo_result_sat_l (ZF.modelsKP hZF) _).mpr
    ⟨H, seq, W, Y, A, Q, e, hw, level, wn, rn, pool, yx, ly, wy, ry, sizes, small, images, exactness, boundW, cW, R_W, model, certificate⟩

/-- 反射规则直接构造原池内的共同秩段；读取只使用 KP 与实际反射语句。 -/
theorem eo_owned_l (hKP : M.Models KP)
    (rule : ∀ ρ : Env M 0, Formula.satisfies ρ eo_kernel_m)
    {ω κ K L X R F δ c d N S j θ α B : M.Domain}
    (source : Ep_source_d (kp_pair_l hKP) ω κ K X R)
    (rank : V_d (kp_pair_l hKP) δ X) (height : M.IsLimitOrdinal δ)
    (family : Em_source_d ω κ L X F) (ord : M.IsOrdinal κ)
    (hm : Smem_d (kp_pair_l hKP) c X R) (hn : Smem_d (kp_pair_l hKP) d N S)
    (card : Sc_inaccessible_d ω X L) (strength : Ex_strength_d (kp_pair_l hKP) ω κ L X F)
    (image : Rd_entry_d κ θ j) (bound : M.MemberSubset L θ)
    (haL : M.mem α L) (ha : M.IsLimitOrdinal α) (rankB : V_d (kp_pair_l hKP) α B) (hkB : M.mem κ B)
    (ultra : It_ultra_d (kp_pair_l hKP) ω κ L F c d j) :
    ∃ W Y A Q e, V_d (kp_pair_l hKP) L W ∧ Er_level_d X L W ∧ M.mem W N ∧ Vr_d N L W ∧
      Eb_collapse_d ω κ L K X B F A Q Y e ∧
      M.mem Y X ∧ M.mem L Y ∧ M.mem W Y ∧ Vr_d Y L W ∧ Sc_rank_size_d (kp_pair_l hKP) Y L ∧ Sc_small_d Y W ∧
      Eo_image_d (kp_pair_l hKP) ω κ L X F j B W A e ∧ Es_strength_d X L Y ∧ Sc_bound_d W ∧
      ∃ cW R_W, Smem_d (kp_pair_l hKP) cW W R_W ∧ Zc_model_d (kp_pair_l hKP) ω cW W R_W := by
  let p : Fin 16 → M.Domain := fun i => [ω,κ,K,L,X,R,F,δ,c,d,N,S,j,θ,α,B].get i
  let ρ : Env M 16 := ⟨p, fun _ => ω⟩
  have seed : Formula.satisfies ρ eo_seed0_m := by
    simp only [eo_seed0_m, Formula.satisfies_conj_iff, ep_source_sat_l hKP,
      v_sigma_sat_l hKP, Formula.satisfies_isLimitOrdinal_iff, em_source_sat_l hKP.1, Formula.satisfies_isOrdinal_iff,
      smem_sat_l (kp_pair_l hKP), rd_entry0_sat_l hKP.1, Formula.satisfies_subset_iff,
      Formula.satisfies_mem_iff, it_ultra_sat_l (kp_pair_l hKP) hKP.1]
    exact ⟨source, rank, height, family, ord, hm, hn,
      (ex_inaccessible_sat_l ρ (.bound 0) (.bound 4) (.bound 3) source.transitive).mpr card,
      (ex_strength_sat_l hKP ρ (.bound 0) (.bound 1) (.bound 3) (.bound 4) (.bound 6) source).mpr strength,
      image, bound, haL, ha, rankB, hkB, ultra⟩
  have out := (Formula.satisfies_imp_iff ..).mp
    ((Formula.satisfies_forallClosure_iff (ℳ := M) ρ.free (.imp eo_seed0_m eo_result0_m)).mp
      (rule ⟨Fin.elim0, ρ.free⟩) ρ.bound) seed
  obtain ⟨_, _, W, Y, A, Q, e, result⟩ := (eo_result_sat_l hKP ρ).mp out
  exact ⟨W, Y, A, Q, e, result⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原一步证书生成两侧共同秩段及递归闭包

从原源理论、所属扩展器和共同层构造全部有限支撑的实际系统与原关系极限。
内部一步证书只在所属模型内解释；有限规则产生同一支撑秩段及其有界池，
实际求值图给出两侧全称秩、小性与子集闭包。切片的关系码、有限空间、
相对幂集与完整内部分离一并构造，根图仍来自原始给定模型。
原短扩展器只在证书的小秩源中判断，再由秩闭包提升到所属模型。
所属模型只需 KP 与这条实际反射规则，新层的 ZFC 证书由规则构造。
外部树边没有整体传递坍塌或可数闭性前提。所属侧有界 ω 闭性作为独立条件时，
同一收集界给出新切片的完整外部 ω 闭性，并在高模型的共同层内实现全部这样的序列。
每个原支撑的坐标值被识别为其所属侧实现像；应用等式仍使用同一全局常值图。
当前源完整 ω 闭且所属侧有界 ω 闭时，实际函数与支撑求值给出整个高模型的完整 ω 闭性。
原根的小关系坍塌句子也沿同一个完整初等根图传入新高模型。
返回同一原池及其求值、坍塌和实现图，连同共同秩层上的实际限制，供复制继续使用。
完整池的常值图方块及全部相对公式的传输也保留，供跨模型子类型直接读取。
共同秩段图实现原模型在支撑以下的全部子集，支撑处的原缺失子集在整个新模型中仍无实现。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.raw_rank_cut_l {ω c X R c' Y S q Γ H k N S₀ z c₁ : M.Domain}
    (hω : M.IsOmega ω) (ex : Rf_ext_d I X R) (mx : Smdl_d I c X R)
    (theory : Sc_theory_d I ω X R) (collection : Sc_collection_d I ω X R)
    (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (owner : Smdl_d I c₁ N S₀)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := S₀) nx).Models KP)
    (ownedRule : ∀ ρ : Env (smdl_structure_l I (R := S₀) nx) 0, Formula.satisfies ρ eo_kernel_m)
    (U₀ w ξ ℓ e α β X' K' R' δ cN dN N' S' jN θ : (smdl_structure_l I (R := S₀) nx).Domain)
    (numbers : Rr_layer_d I ω N S₀ w.val z) (finite : Fs_read_d w U₀)
    (products : ∀ m d : (smdl_structure_l I (R := S₀) nx).Domain,
      (smdl_structure_l I (R := S₀) nx).mem m w → Ep_space_d ξ m d →
      ∃ P : (smdl_structure_l I (R := S₀) nx).Domain, (smdl_structure_l I (R := S₀) nx).mem P U₀ ∧
        (smdl_structure_l I (R := S₀) nx).IsCartesianProduct (kp_pair_l hN) P d β)
    (carrier₀ : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U₀.val S₀)
    (oc : Rr_closed_d I N S₀ U₀.val) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image₀ : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred₀ : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x S₀ ∧ Rd_entry_d s v k)
    (closed : Rr_closed_d I Y S H) (currentSmall : Rr_small_d I Y S H)
    (hβU₀ : (smdl_structure_l I (R := S₀) nx).mem β U₀)
    (hξB : (smdl_structure_l I (R := S₀) nx).mem ξ β)
    (source : Ep_source_d (kp_pair_l hN) w ξ K' X' R')
    (rank : V_d (kp_pair_l hN) δ X')
    (height : (smdl_structure_l I (R := S₀) nx).IsLimitOrdinal δ)
    (hm : Smem_d (kp_pair_l hN) cN X' R')
    (hn : Smem_d (kp_pair_l hN) dN N' S')
    (ultra : It_ultra_d (kp_pair_l hN) w ξ ℓ e cN dN jN)
    (card : Sc_inaccessible_d w X' ℓ) (strength : Ex_strength_d (kp_pair_l hN) w ξ ℓ X' e)
    (hξθ : Rd_entry_d ξ θ jN) (bound : (smdl_structure_l I (R := S₀) nx).MemberSubset ℓ θ)
    (hαL : (smdl_structure_l I (R := S₀) nx).mem α ℓ)
    (hα : (smdl_structure_l I (R := S₀) nx).IsLimitOrdinal α)
    (rankB : V_d (kp_pair_l hN) α β)
    (loc : It_local_d (kp_pair_l hN) w X' R' ξ ℓ e) :
    Er_rank_cut_d hZF ω c X R c' Y S q Γ k N S₀ z c₁ nx hN U₀ w ξ ℓ e β X' K' jN := by
  let N₀ := smdl_structure_l I (R := S₀) nx
  let KpN := kp_pair_l hN
  have actual := loc.rank_absolute_l hN source.omega rank height source.code
  have ownerLocal := it_local_short_l I nx KpN hN.1 actual
  have nativeTrans := v_transitive_l KpN rankB
  have hξU₀ := finite.transitive β hβU₀ ξ hξB
  -- 各有限 κ 幂是原有限列空间的子集；给定秩层直接提供其实际幂集。
  have powers (n D : N₀.Domain) (hn : N₀.mem n w) (space : Ep_space_d ξ n D) :
      ∃ P, N₀.IsPowerSetOf P D :=
    v_power_exists_l KpN hN rank (v_subset_mem_l KpN rank source.finite.mem_l
      (fun s hs => ((source.finite_l hN) s).mpr ⟨n, hn, fn0_function_l hN ((space s).mp hs)⟩))
  -- 两个有限幂的乘积是原 d×β 的子集；同一秩 β 容纳全部内部有限 κ 幂。
  have hwβ := v_subset_mem_l KpN rankB hξB source.below
  have space_mem (m d : N₀.Domain) (hmw : N₀.mem m w) (space : Ep_space_d ξ m d) : N₀.mem d β := by
    obtain ⟨D, hD, full⟩ := v_fspace_exists_l KpN hN rankB hα (nativeTrans w hwβ m hmw) hξB
    exact hN.1.eq_of_same_members D d (fun x => (full x).trans (space x).symm) ▸ hD
  have finiteProduct (m n d f : N₀.Domain) (hmw : N₀.mem m w) (hnw : N₀.mem n w)
      (ds : Ep_space_d ξ m d) (fs : Ep_space_d ξ n f) :
      ∃ P, N₀.mem P U₀ ∧ N₀.IsCartesianProduct KpN P d f := by
    have hf := space_mem n f hnw fs
    obtain ⟨Q, hQ, wide⟩ := products m d hmw ds
    obtain ⟨P, prod⟩ := KP.kprod_exists_l hN d f
    have sub : N₀.MemberSubset P Q := by
      intro x hx
      obtain ⟨a, ha, b, hb, pair⟩ := (prod x).mp hx
      exact (wide x).mpr ⟨a, ha, b, nativeTrans f hf b hb, pair⟩
    exact ⟨P, oc Q.val P.val Q.property P.property hQ (fun x hx => sub ⟨x, hx⟩), prod⟩
  -- 全支撑系统、极限和两条实际嵌入都在此构造，不再作为秩切的外部输入。
  obtain ⟨L, J, O, Z, A, p, T, V, r, o, C, W, j, q', length, system, diagram, limit, next, targetTheory, targetCollection,
    elementary, embed, root, constants, nextTheory, rootGraph, _⟩ :=
    ownerLocal.code_limit_l hZFC hω ex mx theory collection model hq nx hN U₀ w ξ ℓ e
      numbers finite powers finiteProduct carrier₀ oc fk image₀ pred₀ closed currentSmall hξU₀
  obtain ⟨b, _, hβb⟩ := fk.1.2.2 β.val ((carrier₀ β.val).mpr ⟨β.property, hβU₀⟩)
  obtain ⟨H₁, _, hbH⟩ := embed.1.1.2.2 b (fk.1.output_mem_of_pairMember hβb)
  obtain ⟨a₀, D₀, f₀, ff₀, constant, fv⟩ := constants b H₁ hbH
  -- 操作的所属源与指定前驱由原模型码绑定；同一原关系极限成为真实树边。
  obtain ⟨r₀, hr₀⟩ := (I).total ℓ.val e.val
  obtain ⟨p₀, hp₀⟩ := (I).total ξ.val r₀
  have payload : It_payload_d p₀ ξ.val ℓ.val e.val := ⟨r₀, hp₀, hr₀⟩
  have agreement := er_agree_layer_l I nx hN.1 w U₀ ξ numbers finite carrier₀ fk image₀ pred₀ oc closed hξU₀
  have active : It_active_d hZF ω c₁ c' o j p₀ :=
    ⟨ξ.val, ℓ.val, e.val, N, S₀, Y, S, payload, owner, model,
      w.val, z, Γ, k, L, J, O, Z, A, p, T, V, r, C, W,
      ownerLocal, numbers, agreement,
      length, system, diagram, limit, next, embed, constants⟩
  have family := actual.measures.source_l hN powers X'
  obtain ⟨U, Y', A', Q', e', hu, level, _, _, owned, _, hℓY, hUY, rankYU, _, small, images, exactness, rangeBound, cU, R_U, mu, certificate⟩ :=
    eo_owned_l hN ownedRule
      source rank height family actual.critical.1 hm hn card strength hξθ bound hαL hα rankB hξB ultra
  have hβX := source.transitive U level.member β images.member
  refine ⟨L, J, O, Z, A, p, T, V, r, o, C, W, j, q', p₀,
    finite, oc, carrier₀, hβU₀, hβX, nativeTrans, products, length, system, diagram, limit, next, targetTheory, targetCollection,
    elementary, embed, root, constants, agreement, payload, active, nextTheory, rootGraph, ?_⟩
  have ext : Rf_ext_d I Y S := hq.extensional_l hZF hω mx model ex
  have parentTheory := theory.map_l I hZF hω mx model hq
  obtain ⟨D₁, Γ₁, s, v, t, nodes, carrier, sf, nativeGraph, vf, values, decode, _, _, ft, poolGraph, image, pred, compare⟩ :=
    ownerLocal.raw_present_l hZF hω model ext parentTheory nx hN U₀ w ξ ℓ e numbers finite carrier₀ oc
      fk image₀ pred₀ closed hξU₀ length β X' K' δ A' Q' Y' e'
      products (source.finite_l hN) source.finite.mem_l rank height hβX nativeTrans owned
      system diagram limit next embed hβb hbH ff₀ constant fv
  have data := owned
  obtain ⟨Jn, _, _, _, _, pool, indices, _, _, _, _, _, _, _, _, collapse, _⟩ := data
  have yt := collapse.transitive
  obtain ⟨l, hl, hℓl⟩ := ft.1.2.2 ℓ.val ((carrier ℓ.val).mpr ⟨ℓ.property, hℓY⟩)
  obtain ⟨H₂, hH₂, hUH⟩ := ft.1.2.2 U.val ((carrier U.val).mpr ⟨U.property, hUY⟩)
  -- 父容器的全子集闭包由旧共同层回收，再在原所属秩层内判断。
  have closedB := rr_cross_closed_l I nx U₀ β finite.transitive carrier₀ fk image₀ pred₀ closed hβb
    (fun x y hx hy hxβ sub => v_subset_mem_l KpN rankB (show N₀.mem ⟨x, hx⟩ β from hxβ)
      (show N₀.MemberSubset ⟨y, hy⟩ ⟨x, hx⟩ from fun a ha => sub a.val a.property ha))
  have closedH := (embed.rr_closed_l I hZF hω model next hbH).mp closedB
  have lengthTrans := (v_ordinal_l KpN hu).transitive
  have fullExact := er_exact_l (ZF.modelsKP hZF) nx hN.1 X' Y' ℓ yt carrier ft image pred closedH hℓl
    lengthTrans (fun a x ha sub => source.transitive U level.member x
      (v_subset_mem_l KpN hu (KP.v_ordinal_subset_l hN hu a ha) sub)) exactness
  have parentCollection := (sc_collection_iff_l I hZF hω mx model
    (ex.native_l I mx.2.1) (ext.native_l I model.2.1) hq).mp collection
  have nextExt : Rf_ext_d I C W := embed.extensional_l hZF hω model next ext
  obtain ⟨targetRank, targetClosed, targetSmall⟩ :=
    rr_native_rank_l hZF nx next.2.1 hN (nextExt.native_l I next.2.1) Y' ℓ U yt carrier ft image pred closedH
      hℓY hUY hℓl hUH rankYU small
  -- 原所属侧使用其真实 V_L；新秩段两侧都不需要背景传递坍塌。
  have sourceRank : Rr_rank_d I N S₀ ℓ.val U.val := by
    rcases ℓ with ⟨l₀, hl₀⟩
    rcases U with ⟨u₀, hu₀⟩
    let ρ : Env N₀ 2 := ⟨Fin.cases ⟨u₀, hu₀⟩ (fun _ => ⟨l₀, hl₀⟩), fun _ => ⟨l₀, hl₀⟩⟩
    exact ⟨hl₀, hu₀, (v_sigma_sat_l hN ρ (.bound 1) .newest).mpr hu⟩
  have sourceClosed : Rr_closed_d I N S₀ U.val := by
    intro x y hx hy hxU sub
    have sub' : N₀.MemberSubset ⟨y, hy⟩ ⟨x, hx⟩ := fun z hz => sub z.val z.property hz
    exact v_subset_mem_l KpN hu (show N₀.mem ⟨x, hx⟩ U from hxU) sub'
  have sourceSmall : Rr_small_d I N S₀ U.val := by
    intro x hx hxU
    let x' : N₀.Domain := ⟨x, hx⟩
    obtain ⟨μ, f, _, _, idx⟩ := small.mono_l ((v_transitive_l KpN hu) x' hxU)
    refine ⟨hx, ?_⟩
    change Formula.satisfies (⟨fun _ => x', fun _ => x'⟩ : Env N₀ 1) (sc_small_m .newest)
    simp only [sc_small_m, Formula.satisfies_exists_iff]
    exact ⟨μ, f, (sc_index_sat_l hN ..).mpr idx⟩
  let ρ : Env M 2 := ⟨Fin.cases U.val (fun _ => S₀), fun _ => N⟩
  let φ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨D, ds⟩ := ZF.separation_exists_d hZF φ ρ N
  have dc x : M.mem x D ↔ M.mem x N ∧ Rd_entry_d x U.val S₀ :=
    (ds x).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
  have inside x (hx : M.mem x D) : M.mem x Γ₁ :=
    (carrier x).mpr ⟨((dc x).mp hx).1, yt U hUY ⟨x, ((dc x).mp hx).1⟩ ((dc x).mp hx).2⟩
  obtain ⟨u, res⟩ := ZF.exists_restriction hZF I t D
  have fi : M.IsSetInjectionFromTo I u D C :=
    ⟨res.isSetFunctionFromTo ft.1 inside, fun x y E hx hy => ft.2 x y E ((res.2 x E).mp hx).2 ((res.2 y E).mp hy).2⟩
  have belowD a ha haL := (dc a).mpr ⟨ha, KP.v_ordinal_subset_l hN hu ⟨a, ha⟩ haL⟩
  have cutExact := fullExact.restrict_l (ZF.modelsKP hZF) nx ℓ lengthTrans res belowD
  have endpoint : Er_rep_d N S₀ C W u ℓ.val l :=
    (er_rep_restrict_l (ZF.modelsKP hZF) res belowD).mpr
      ((er_subset_read_l (ZF.modelsKP hZF) nx hN.1 Y' ℓ yt carrier ft image pred closedH hℓl
        ℓ l (fun _ h => h)).mpr hℓl)
  have full E : Rd_entry_d E H₂ W ↔ ∃ x, M.mem x D ∧ Rd_entry_d x E u := by
    apply (pred U.val H₂ hUH E).trans
    constructor
    · rintro ⟨x, hxU, hxE⟩
      have hxD := (dc x).mpr ⟨((carrier x).mp (ft.1.input_mem_of_pairMember hxE)).1, hxU⟩
      exact ⟨x, hxD, (res.2 x E).mpr ⟨hxD, hxE⟩⟩
    · rintro ⟨x, hxD, hxE⟩
      exact ⟨x, ((dc x).mp hxD).2, ((res.2 x E).mp hxE).2⟩
  have prev x E (hxE : Rd_entry_d x E u) P :
      Rd_entry_d P E W ↔ ∃ y, Rd_entry_d y x S₀ ∧ Rd_entry_d y P u := by
    obtain ⟨hxD, hxE⟩ := (res.2 x E).mp hxE
    apply (pred x E hxE P).trans
    constructor
    · rintro ⟨y, hyx, hyP⟩
      have hyN := ((carrier y).mp (ft.1.input_mem_of_pairMember hyP)).1
      have hyD := (dc y).mpr ⟨hyN, (v_transitive_l KpN hu)
        ⟨x, ((dc x).mp hxD).1⟩ ((dc x).mp hxD).2 ⟨y, hyN⟩ hyx⟩
      exact ⟨y, hyx, (res.2 y P).mpr ⟨hyD, hyP⟩⟩
    · rintro ⟨y, hyx, hyP⟩
      exact ⟨y, hyx, ((res.2 y P).mp hyP).2⟩
  have lengthLimit : N₀.IsLimitOrdinal ℓ := (sc_v_inaccessible_up_l hN height rank card).2.1.isLimitOrdinal
  have common : Ic_common_d I N S₀ C W ℓ.val l U.val H₂ D u :=
    ⟨sourceRank, targetRank,
      ⟨fun _ => ℓ.property, (Formula.satisfies_isLimitOrdinal_iff ..).mpr lengthLimit⟩,
      dc, fi, full, prev, sourceClosed, targetClosed, endpoint, cutExact⟩
  -- 完整池中的常值像先对应实际超幂边，再限制到共同秩段。
  have commute_full (x y : N₀.Domain) b E (hx : N₀.mem x β)
      (hxy : Rd_entry_d x y jN) (hxb : Rd_entry_d x.val b k) :
      Rd_entry_d y.val E t ↔ Rd_entry_d b E j := by
    have old := (images.constants x y hx).mpr hxy
    have lift E (hbE : Rd_entry_d b E j) : Rd_entry_d y.val E t := by
      obtain ⟨a, D₀, f, ff, fc, fv⟩ := constants b E hbE
      exact compare x y b E a D₀ f old hxb ff fc fv
    refine ⟨fun hyE => ?_, lift E⟩
    obtain ⟨E', _, hbE'⟩ := embed.1.1.2.2 b (fk.1.output_mem_of_pairMember hxb)
    exact ft.1.1.2 y.val E' E (lift E' hbE') hyE ▸ hbE'
  have commute (x y : N₀.Domain) b E (hx : N₀.mem x β) (hy : N₀.mem y U)
      (hxy : Rd_entry_d x y jN) (hxb : Rd_entry_d x.val b k) :
      Rd_entry_d y.val E u ↔ Rd_entry_d b E j :=
    (res.2 y.val E).trans ((and_iff_right ((dc y.val).mpr ⟨y.property, hy⟩)).trans
      (commute_full x y b E hx hxy hxb))
  -- 实际分离切片关系；后续程序解释沿同一 u 回收，绝不把对象码视作背景集合。
  have hξU := (v_transitive_l KpN hu) β images.member ξ hξB
  obtain ⟨bκ, _, hξb⟩ := fk.1.2.2 ξ.val ((carrier₀ ξ.val).mpr ⟨ξ.property, hξU₀⟩)
  obtain ⟨κ', _, hκj⟩ := embed.1.1.2.2 bκ (fk.1.output_mem_of_pairMember hξb)
  obtain ⟨a, Dκ, fκ, ffκ, fcκ, fvκ⟩ := constants bκ κ' hκj
  have hθκ := compare ξ θ bκ κ' a Dκ fκ ((images.constants ξ θ hξB).mpr hξθ) hξb ffκ fcκ fvκ
  have support E (hE : Rd_entry_d E l W) : Rd_entry_d E κ' W := by
    obtain ⟨x, hxl, hxE⟩ := (pred ℓ.val l hℓl E).mp hE
    let x' : N₀.Domain := ⟨x, ((carrier x).mp (ft.1.input_mem_of_pairMember hxE)).1⟩
    exact (pred θ.val κ' hθκ E).mpr ⟨x, bound x' hxl, hxE⟩
  obtain ⟨κ₀, _, hξκ⟩ := fi.1.2.2 ξ.val ((dc ξ.val).mpr ⟨ξ.property, hξU⟩)
  have hξt := ((res.2 ξ.val κ₀).mp hξκ).2
  have below : Rd_entry_d κ₀ l W := (pred ℓ.val l hℓl κ₀).mpr ⟨ξ.val, actual.above, hξt⟩
  have moved : κ₀ ≠ κ' := by
    intro eq
    have eq' : ξ = θ := Subtype.ext (ft.2 ξ.val θ.val κ' (eq ▸ hξt) hθκ)
    exact KP.mem_irrefl_d hN θ (eq' ▸ bound ξ actual.above)
  let ψ : BinarySchema 1 := { body := rd_entry0_m (.bound 1) .newest (.bound 2) }
  let η : Env M 1 := ⟨fun _ => S₀, fun _ => S₀⟩
  obtain ⟨cD, R_D, cut, rel⟩ := smdl_exists_l I hZF ψ η ⟨ξ.val, (dc ξ.val).mpr ⟨ξ.property, hξU⟩⟩
  have read x y : Rd_entry_d x y R_D ↔ M.mem x D ∧ M.mem y D ∧ Rd_entry_d x y S₀ :=
    (rel x y).trans (and_congr_right fun _ => and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
  have atoms x y E P (hx : Rd_entry_d x E u) (hy : Rd_entry_d y P u) :
      Rd_entry_d x y R_D ↔ Rd_entry_d E P W := by
    apply (read x y).trans
    exact ⟨fun h => (prev y P hy E).mpr ⟨x, h.2.2, hx⟩, fun h => by
      obtain ⟨z, hz, hzE⟩ := (prev y P hy E).mp h
      exact ⟨fi.1.input_mem_of_pairMember hx, fi.1.input_mem_of_pairMember hy, fi.2 z x E hzE hx ▸ hz⟩⟩
  obtain ⟨_, regular, _⟩ := sc_v_inaccessible_up_l hN height rank card
  -- 原规则保留同一个低秩层与固定证明；这里只代入实际坐标条款。
  obtain ⟨P, rankP, hPβ, fix⟩ := images.fixed
  have hPU := (v_transitive_l KpN hu) β images.member P hPβ
  have fixed := fix (actual.coherent.source_l KpN X') actual.atoms (actual.normal.source_l X') (by
    intro n a V D B hn ha ds haV _ sub haB
    exact (actual.principal n a V hn ha haV B).mpr ⟨fun s hs => (ds s).mp (sub s hs), haB⟩)
  have keep (x : N₀.Domain) b E (hx : N₀.mem x P) (hxb : Rd_entry_d x.val b k) :
      Rd_entry_d x.val E u ↔ Rd_entry_d b E j :=
    commute x x b E (nativeTrans P hPβ x hx) ((v_transitive_l KpN hu) P hPU x hx) (fixed x hx) hxb
  -- 两侧 κ 都由原模型的序数通过完整前驱解释得到；对象码不作背景序数使用。
  have ord₀ : Rr_truth_d I Y S (KP.ord0_m .newest) (fun _ : Fin 1 => bκ) := by
    let ν : Nonempty {x : N₀.Domain // N₀.mem x U₀} := ⟨⟨ξ, hξU₀⟩⟩
    let a : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨bκ, fk.1.output_mem_of_pairMember hξb⟩
    let ρ : Env (rt_model_l U₀ ν) 1 := ⟨fun _ => ⟨ξ, hξU₀⟩, fun _ => ⟨ξ, hξU₀⟩⟩
    apply (rr_truth_native_l I model.2.1 _ (by simp -implicitDefEqProofs) (fun _ => a)).mpr
    exact (rr_native_delta_l I nx model.2.1 U₀ finite.transitive ν carrier₀ fk pred₀
      (KP.ord0_m .newest) (by simp -implicitDefEqProofs) (KP.ord0_delta_l .newest)
      ρ ⟨fun _ => a, fun _ => a⟩ (fun _ => hξb)).mp ((KP.ord0_sat_l hN _ .newest).mpr actual.critical.1)
  have ord₁ : Rr_truth_d I C W (KP.ord0_m .newest) (fun _ : Fin 1 => κ₀) := by
    let ν : Nonempty {x : N₀.Domain // N₀.mem x U} := ⟨⟨ξ, hξU⟩⟩
    let a : (smdl_structure_l I (R := W) next.2.1).Domain := ⟨κ₀, fi.1.output_mem_of_pairMember hξκ⟩
    let ρ : Env (rt_model_l U ν) 1 := ⟨fun _ => ⟨ξ, hξU⟩, fun _ => ⟨ξ, hξU⟩⟩
    apply (rr_truth_native_l I next.2.1 _ (by simp -implicitDefEqProofs) (fun _ => a)).mpr
    exact (rr_native_delta_l I nx next.2.1 U (v_transitive_l KpN hu) ν dc fi prev
      (KP.ord0_m .newest) (by simp -implicitDefEqProofs) (KP.ord0_delta_l .newest)
      ρ ⟨fun _ => a, fun _ => a⟩ (fun _ => hξκ)).mp ((KP.ord0_sat_l hN _ .newest).mpr actual.critical.1)
  have ord₂ := ord₀.map_l I hZF hω model next embed
    (by simp -implicitDefEqProofs) (fun _ => hκj)
  -- 临界点以下的原序数都属于真实 V_κ；同一常值图逐点交换两侧解释。
  have ord_fix x b E (hx : M.mem x N) (hxκ : Rd_entry_d x ξ.val S₀) (hxb : Rd_entry_d x b k) :
      Rd_entry_d x E u ↔ Rd_entry_d b E j :=
    keep ⟨x, hx⟩ b E (KP.v_ordinal_subset_l hN rankP ⟨x, hx⟩ hxκ) hxb
  -- 下界层本身可以移动；这里只把其全部成员沿实际树边相互识别。
  have low_img γ (lower : It_lower_d I γ N S₀ ξ.val) :
      It_lower_d I γ Y S bκ ∧ It_lower_d I γ C W κ₀ ∧
      ∃ h₀ h₁ z₀ z₁, Rr_layer_d I γ Y S h₀ z₀ ∧ Rr_layer_d I γ C W h₁ z₁ ∧
        ∀ x b, Rd_entry_d x b z₀ → ∀ E, Rd_entry_d x E z₁ ↔ Rd_entry_d b E j := by
    obtain ⟨b, z₀, layer, low⟩ := lower
    have hbΓ := (carrier₀ b).mpr ⟨layer.member,
      oc ξ.val b ξ.property layer.member hξU₀ (fun x _ => low x)⟩
    have hbD := (dc b).mpr ⟨layer.member,
      sourceClosed ξ.val b ξ.property layer.member hξU (fun x _ => low x)⟩
    have below x y (hxy : Rd_entry_d x y z₀) : Rd_entry_d y ξ.val S₀ :=
      low y ((layer.image y).mpr ⟨x, layer.injection.1.input_mem_of_pairMember hxy, hxy⟩)
    have in₀ x y (hxy : Rd_entry_d x y z₀) : M.mem y Γ :=
      (carrier₀ y).mpr ⟨layer.injection.1.output_mem_of_pairMember hxy,
        finite.transitive ξ hξU₀ ⟨y, layer.injection.1.output_mem_of_pairMember hxy⟩ (below x y hxy)⟩
    have in₁ x y (hxy : Rd_entry_d x y z₀) : M.mem y D :=
      (dc y).mpr ⟨layer.injection.1.output_mem_of_pairMember hxy,
        (v_transitive_l KpN hu) ξ hξU ⟨y, layer.injection.1.output_mem_of_pairMember hxy⟩ (below x y hxy)⟩
    obtain ⟨b₀, _, hbb₀⟩ := fk.1.2.2 b hbΓ
    obtain ⟨b₁, _, hbb₁⟩ := fi.1.2.2 b hbD
    obtain ⟨s, left, ls⟩ := layer.image_l (ZF.modelsKP hZF) fk in₀ pred₀ hbb₀
    obtain ⟨t, right, rt⟩ := layer.image_l (ZF.modelsKP hZF) fi in₁ prev hbb₁
    have lo₀ y (hy : Rd_entry_d y b₀ S) : Rd_entry_d y bκ S := by
      obtain ⟨x, hx, hxy⟩ := (pred₀ b b₀ hbb₀ y).mp hy
      exact (pred₀ ξ.val bκ hξb y).mpr ⟨x, low x hx, hxy⟩
    have lo₁ E (hE : Rd_entry_d E b₁ W) : Rd_entry_d E κ₀ W := by
      obtain ⟨x, hx, hxE⟩ := (prev b b₁ hbb₁ E).mp hE
      exact (prev ξ.val κ₀ hξκ E).mpr ⟨x, low x hx, hxE⟩
    refine ⟨⟨b₀, s, left, lo₀⟩, ⟨b₁, t, right, lo₁⟩, b₀, b₁, s, t, left, right, ?_⟩
    intro x y hxy E
    obtain ⟨a, hxa, hay⟩ := (ls x y).mp hxy
    apply Iff.trans ?_ (ord_fix a y E (layer.injection.1.output_mem_of_pairMember hxa) (below x a hxa) hay)
    exact (rt x E).trans ⟨fun ⟨a', hxa', haE⟩ => layer.injection.1.1.2 x a' a hxa' hxa ▸ haE,
      fun haE => ⟨a, hxa, haE⟩⟩
  -- 原秩层先在所属模型中比较，再沿同一 u 解释；根图只逐点固定层的成员。
  have anchor_step γ B a V s t (height₀ : Rr_layer_d I γ N S₀ a s)
      (layer₀ : Rr_layer_d I B N S₀ V t) (rank₀ : Rr_rank_d I N S₀ a V)
      (bound₀ : ∀ x, Rd_entry_d x a S₀ → Rd_entry_d x ξ.val S₀)
      (prior : Tg_anchor_d I γ B Y S q) : Tg_anchor_d I γ B C W q' := by
    let a₀ : N₀.Domain := ⟨a, height₀.member⟩
    let V₀ : N₀.Domain := ⟨V, layer₀.member⟩
    have rk : V_d KpN a₀ V₀ := (rr_rank_native_l I nx hN a₀ V₀).mp rank₀
    have lo : N₀.MemberSubset a₀ ξ := fun x hx => bound₀ x.val hx
    have sub := (KP.v_compare_l hN rk rankP lo).1
    have haβ := v_subset_mem_l KpN rankB hξB lo
    have hVβ := v_subset_mem_l KpN rankB hPβ sub
    have hVU₀ := finite.transitive β hβU₀ V₀ hVβ
    have haU := (v_transitive_l KpN hu) β images.member a₀ haβ
    have hVU := (v_transitive_l KpN hu) β images.member V₀ hVβ
    obtain ⟨F₀, hFβ, cert⟩ := KP.v_history_inside_l hN rankB hα haβ hVβ rk
    have rankU : Vr_d U a₀ V₀ :=
      ⟨V₀, F₀, hVU, (v_transitive_l KpN hu) β images.member F₀ hFβ, fun x _ => cert x⟩
    have in₀ x y (hxy : Rd_entry_d x y t) : M.mem y Γ :=
      (carrier₀ y).mpr ⟨layer₀.injection.1.output_mem_of_pairMember hxy,
        finite.transitive V₀ hVU₀ ⟨y, layer₀.injection.1.output_mem_of_pairMember hxy⟩
          ((layer₀.image y).mpr ⟨x, layer₀.injection.1.input_mem_of_pairMember hxy, hxy⟩)⟩
    have in₁ x y (hxy : Rd_entry_d x y t) : M.mem y D :=
      (dc y).mpr ⟨layer₀.injection.1.output_mem_of_pairMember hxy,
        (v_transitive_l KpN hu) V₀ hVU ⟨y, layer₀.injection.1.output_mem_of_pairMember hxy⟩
          ((layer₀.image y).mpr ⟨x, layer₀.injection.1.input_mem_of_pairMember hxy, hxy⟩)⟩
    have in₂ x y (hxy : Rd_entry_d x y s) : M.mem y D :=
      (dc y).mpr ⟨height₀.injection.1.output_mem_of_pairMember hxy,
        (v_transitive_l KpN hu) a₀ haU ⟨y, height₀.injection.1.output_mem_of_pairMember hxy⟩
          ((height₀.image y).mpr ⟨x, height₀.injection.1.input_mem_of_pairMember hxy, hxy⟩)⟩
    obtain ⟨b₀, _, e₀⟩ := fk.1.2.2 V ((carrier₀ V).mpr ⟨layer₀.member, hVU₀⟩)
    obtain ⟨b₁, _, e₁⟩ := fi.1.2.2 V ((dc V).mpr ⟨layer₀.member, hVU⟩)
    obtain ⟨a₁, _, e₂⟩ := fi.1.2.2 a ((dc a).mpr ⟨height₀.member, haU⟩)
    obtain ⟨t₀, left, g₀⟩ := layer₀.image_l (ZF.modelsKP hZF) fk in₀ pred₀ e₀
    obtain ⟨t₁, right, g₁⟩ := layer₀.image_l (ZF.modelsKP hZF) fi in₁ prev e₁
    obtain ⟨s₁, height₁, _⟩ := height₀.image_l (ZF.modelsKP hZF) fi in₂ prev e₂
    have rk₁ := rr_native_rank_value_l I nx next.2.1
      (nextExt.native_l I next.2.1) U a₀ V₀ (v_transitive_l KpN hu)
      dc fi full prev targetClosed haU hVU e₂ e₁
      ((vr_sat_l hN (v_transitive_l KpN hu) _ _ (.bound 1) .newest).mpr rankU)
    have square : It_comp_d q j q' := ⟨root.1.1.1.1, fun x E => (rootGraph x E).trans
      ⟨And.right, fun ⟨y, hxy, hyE⟩ => ⟨hq.1.1.input_mem_of_pairMember hxy, y, hxy, hyE⟩⟩⟩
    apply prior.extend_l (ZF.modelsKP hZF) ext left height₁ right rk₁ (comp := square)
    intro x b hxb E
    obtain ⟨y, hxy, hyb⟩ := (g₀ x b).mp hxb
    have hyP := sub ⟨y, layer₀.injection.1.output_mem_of_pairMember hxy⟩
      ((layer₀.image y).mpr ⟨x, layer₀.injection.1.input_mem_of_pairMember hxy, hxy⟩)
    apply Iff.trans ?_ (keep ⟨y, layer₀.injection.1.output_mem_of_pairMember hxy⟩ b E hyP hyb)
    exact (g₁ x E).trans ⟨fun ⟨y', hxy', hyE⟩ => layer₀.injection.1.1.2 x y' y hxy' hxy ▸ hyE,
      fun hyE => ⟨y, hxy, hyE⟩⟩
  have hwU := (v_transitive_l KpN hu) β images.member w hwβ
  let nu : Nonempty {x : N₀.Domain // N₀.mem x U} := ⟨⟨w, hwU⟩⟩
  -- 固定公理来自原证书；分离与收集在 KP 中由实际秩闭包和关系见证界读取。
  have base : ∀ ρ : Env (rt_model_l U nu) 0, Formula.satisfies ρ zc_base_m := fun ρ =>
    (smem_formula_l KpN mu nu zc_base_m ⟨ρ.bound, ρ.free⟩).mpr (certificate.base _)
  have nativeCut := rangeBound.models_l hN (v_transitive_l KpN hu)
    (fun D hd A sub => v_subset_mem_l KpN hu hd sub) nu base
  have sourceTheory : Sc_theory_d KpN w U R_U := by
    refine ⟨certificate.schemas.separation, fun _ ρ => ?_⟩
    let σ : Env (rt_model_l U nu) 0 := ⟨ρ.bound, ρ.free⟩
    exact (smem_formula_l KpN mu nu sc_algebra_m σ).mp (sc_algebra_models_l nativeCut σ)
  obtain ⟨nativeFinite, cutExt, cutAlgebra, cutFinite⟩ := er_cut_closure_l I nx hN U ℓ w hu
    regular.isLimitOrdinal source.omega hwU (sourceTheory.algebra_l KpN hN (v_transitive_l KpN hu) mu) dc cut read
  have cutTheory := rr_cut_models_l I nx U nu cut.2.1 dc read ZFC nativeCut
  -- 保留同一自然数坐标图；只把其值域读为新秩段的对象码。
  have value n x (hnx : Rd_entry_d n x z) : M.mem x D := by
    have hx := numbers.injection.1.output_mem_of_pairMember hnx
    exact (dc x).mpr ⟨hx, (v_transitive_l KpN hu) w hwU ⟨x, hx⟩
      ((numbers.image x).mpr ⟨n, numbers.injection.1.input_mem_of_pairMember hnx, hnx⟩)⟩
  have fsd : M.IsSetFunctionFromTo I z ω D := ⟨numbers.injection.1.1, numbers.injection.1.2.1,
    fun n hn => (numbers.injection.1.2.2 n hn).imp fun x hx => ⟨value n x hx.2, hx.2⟩⟩
  have hwD := (dc w.val).mpr ⟨w.property, hwU⟩
  have nextNumbers : Rr_layer_d I ω D R_D w.val z := by
    refine ⟨numbers.transitive, hwD, ⟨fsd, numbers.injection.2⟩, ?_, ?_⟩
    · intro x
      constructor
      · intro hx
        exact (numbers.image x).mp ((read x w.val).mp hx).2.2
      · rintro ⟨n, hn, hnx⟩
        exact (read x w.val).mpr ⟨value n x hnx, hwD, (numbers.image x).mpr ⟨n, hn, hnx⟩⟩
    · intro n x hnx y
      constructor
      · intro hy
        exact (numbers.predecessors n x hnx y).mp ((read y x).mp hy).2.2
      · rintro ⟨i, hin, hiy⟩
        exact (read y x).mpr ⟨value i y hiy, value n x hnx, (numbers.predecessors n x hnx y).mpr ⟨i, hin, hiy⟩⟩
  -- 有界可数列先在所属模型中实现；原规则的实际收集界把整张图回收到同一 U。
  have ownExt : Rf_ext_d I N S₀ := fun x hx y hy same =>
    congrArg Subtype.val (hN.1.eq_of_same_members (⟨x, hx⟩ : N₀.Domain) ⟨y, hy⟩ (fun v => same v.val v.property))
  have countable (close : Sc_bounded_omega_closed_d I ω N S₀) : Sc_omega_closed_d I ω D R_D :=
    close.cut_l (ZF.modelsKP hZF) hω nx KpN ownExt w ℓ U numbers hu regular.isLimitOrdinal
      rangeBound hwU dc read nextNumbers
  -- 两侧自然数图由同一个原坐标图复合；固定证书保证原超幂边上的交换式。
  have oldValue n x (hnx : Rd_entry_d n x z) : M.mem x Γ := by
    have hx := numbers.injection.1.output_mem_of_pairMember hnx
    exact (carrier₀ x).mpr ⟨hx, finite.transitive w finite.omega_mem ⟨x, hx⟩
      ((numbers.image x).mpr ⟨n, numbers.injection.1.input_mem_of_pairMember hnx, hnx⟩)⟩
  obtain ⟨w₀, _, hww₀⟩ := fk.1.2.2 w.val ((carrier₀ w.val).mpr ⟨w.property, finite.omega_mem⟩)
  obtain ⟨w₁, _, hww₁⟩ := fi.1.2.2 w.val hwD
  obtain ⟨z₀, oldNumbers, oldGraph⟩ := numbers.image_l (ZF.modelsKP hZF) fk oldValue pred₀ hww₀
  obtain ⟨z₁, newNumbers, newGraph⟩ := numbers.image_l (ZF.modelsKP hZF) fi value prev hww₁
  have omegaEdge := (commute w w w₀ w₁ hwβ hwU images.numbers.1 hww₀).mp hww₁
  have numeric n x (hnx : Rd_entry_d n x z₀) y : Rd_entry_d n y z₁ ↔ Rd_entry_d x y j := by
    obtain ⟨m, hnm, hmx⟩ := (oldGraph n x).mp hnx
    let m' : N₀.Domain := ⟨m, numbers.injection.1.output_mem_of_pairMember hnm⟩
    have hm : N₀.mem m' w :=
      (numbers.image m).mpr ⟨n, numbers.injection.1.input_mem_of_pairMember hnm, hnm⟩
    have step := commute m' m' x y (nativeTrans w hwβ m' hm)
      ((v_transitive_l KpN hu) w hwU m' hm) (images.numbers.2 m' hm) hmx
    apply Iff.trans ?_ step
    exact (newGraph n y).trans ⟨fun ⟨r, hnr, hry⟩ =>
      (show Rd_entry_d m y u from numbers.injection.1.1.2 n r m hnr hnm ▸ hry),
      fun hmy => ⟨m, hnm, hmy⟩⟩
  -- 原根的 ω 像由完整自然数层唯一确定；同一原关系句子沿两条实际根图传输。
  have sequences v t (rootNumbers : Rr_layer_d I ω X R v t) (seq : Sc_sequences_d I v X R) :
      Rd_entry_d v w₀ q ∧ Rd_entry_d v w₁ q' ∧ Sc_sequences_d I w₀ Y S ∧ Sc_sequences_d I w₁ C W := by
    have old := (rootNumbers.omega_map_l I hZF hω mx model hq ex ext oldNumbers).1
    have new := (rootNumbers.omega_map_l I hZF hω mx next root ex nextExt newNumbers).1
    exact ⟨old, new, (sc_sequences_iff_l I hZF hω mx model hq old).mp seq,
      (sc_sequences_iff_l I hZF hω mx next root new).mp seq⟩
  have countableImage (close : Sc_bounded_omega_closed_d I ω N S₀) :=
    close.image_l hZF hω nx KpN ownExt w ℓ U numbers hu regular.isLimitOrdinal rangeBound hwU
      dc fi full prev nextExt hww₁ newGraph
  -- 同一原池中的恒等节点同时决定支撑像和坐标值。
  have coordinate {a₀ n D₀ t₀ a₁ : M.Domain} (m b₀ d₀ : N₀.Domain)
      (ha₀ : M.mem a₀ J) (hn : M.mem n ω) (hnm : Rd_entry_d n m.val z)
      (code : Rr_finite_d I ω L N S₀ z a₀ b₀.val) (fb : Fn0_d m ℓ b₀) (space : Ep_space_d ξ m d₀)
      (dc₀ : ∀ x, M.mem x D₀ ↔ M.mem x N ∧ Rd_entry_d x d₀.val S₀)
      (ft₀ : Fn0_d D₀ Y t₀) (rt₀ : M.IsRestrictionOf I t₀ k D₀) (repr : Ep_repr_d r a₀ t₀ a₁) :
      Rd_entry_d b₀.val a₁ u := by
    have hmw : N₀.mem m w := (numbers.image m.val).mpr ⟨n, hn, hnm⟩
    have hdB := space_mem m d₀ hmw space
    have hdX := source.transitive β hβX d₀ hdB
    obtain ⟨f, fn, id⟩ := fn0_identity_l hN d₀
    have ff := fn.mono_target_l (nativeTrans d₀ hdB)
    obtain ⟨Q, hQ, dq, bq⟩ := v_joint_bound_l KpN rank hdX hβX
    have hfX := v_relation_mem_l KpN rank height hQ (fun x hx => by
      obtain ⟨s, hs, y, hy, pair⟩ := ff.1 x hx
      exact ⟨s, dq s hs, y, bq y hy, pair⟩)
    have data := code
    obtain ⟨i, m₀, _, fα, him, fnα, grα⟩ := data
    let m' : N₀.Domain := ⟨m₀, numbers.injection.1.output_mem_of_pairMember him⟩
    obtain ⟨B, fm⟩ := (rf_fun_native_l I nx hN.1 m' b₀).mp fnα
    have em := congrArg (fun x : N₀.Domain => x.val) (fm.domain_eq_l hN.1 fb)
    have him : Rd_entry_d i m.val z := em ▸ him
    obtain ⟨_, _, _, inj⟩ := (system.indices a₀).mp ha₀
    have inj' := (numbers.function_injective_l hZF hN.1 m ℓ b₀ him fb
      (fα.mono_target_l (fun x hx => ((length x).mp hx).1)) grα).mp inj
    have hbJ := (indices b₀).mpr ⟨m, hmw, fb, inj'⟩
    obtain ⟨x, pair⟩ := KpN.total b₀ f
    have hx := pool.node_l hN (source.finite_l hN) hmw hbJ fb space hdX hfX ff pair
    have hxb := images.coordinates (actual.coherent.source_l KpN X') actual.atoms (actual.normal.source_l X')
      x b₀ f hx pair (fun s y h => ((id s y).mp h).2)
    -- 原恒等函数展开为背景恒等图，再与同一个 k 复合。
    obtain ⟨F, fF, diagonal⟩ := fn0_identity_l (ZF.modelsKP hZF) D₀
    have into x (hx : M.mem x D₀) : M.mem x Γ := (carrier₀ x).mpr ⟨((dc₀ x).mp hx).1,
      finite.transitive β hβU₀ ⟨x, ((dc₀ x).mp hx).1⟩ (nativeTrans d₀ hdB _ ((dc₀ x).mp hx).2)⟩
    have fF := fF.mono_target_l into
    have graph (s y : N₀.Domain) : Rd_entry_d s.val y.val F ↔ Rd_entry_d s y f := by
      apply (diagonal s.val y.val).trans (Iff.trans ?_ (id s y).symm)
      exact ⟨fun ⟨hs, eq⟩ => ⟨((dc₀ s.val).mp hs).2, Subtype.ext eq⟩,
        fun ⟨hs, eq⟩ => ⟨(dc₀ s.val).mpr ⟨s.property, hs⟩, congrArg (fun x : N₀.Domain => x.val) eq⟩⟩
    have comp : Cp0_d D₀ Γ Y F k t₀ := ⟨ft₀, fun s hs => by
      obtain ⟨y, hy, hsy⟩ := ft₀.2.1 s hs
      exact ⟨s, into s hs, y, hy, (diagonal s s).mpr ⟨hs, rfl⟩, ((rt₀.2 s y).mp hsy).2, hsy⟩⟩
    have value := Er_eval_d.write_l hZF nx hN.1 x b₀ f d₀ β code ff pair dc₀ fF graph comp repr
    have hxD := (nodes x.val).mpr ⟨x.property, hx⟩
    have image := (poolGraph b₀.val a₁).mpr ⟨x.val, hxD,
      (rf_val_native_l I nx hN.1 x b₀ e').mpr hxb, value⟩
    have hbU := nativeFinite.functions m ℓ b₀ hmw (KP.v_ordinal_subset_l hN hu) fb
    exact (res.2 b₀.val a₁).mpr ⟨(dc b₀.val).mpr ⟨b₀.property, hbU⟩, image⟩
  have representations : ∀ E, M.mem E C → ∃ b d f a F, M.mem b D ∧ Rf_fun_d I Y S d f ∧
      Rd_entry_d b a u ∧ Rd_entry_d f F j ∧ Rf_val_d I C W a E F := by
    intro E hE
    obtain ⟨x, hxE⟩ := (limit.range E).mp hE
    have hx := (limit.projection.bound_l hxE).1
    obtain ⟨a₀, B, pair, _⟩ := (system.nodes x).mp hx
    have ha := (system.projection.bound_l ((system.index x a₀ B pair).mpr hx)).2
    obtain ⟨n, m, b₀, d₀, D₀, t₀, y₀, a₁, hn, hnm, code, fb, space, dc₀, ft₀, rt₀, _, repr, law, cover, _⟩ :=
      system.application_l hZF hω model ext parentTheory parentCollection nx hN U₀ w ξ ℓ e
        numbers finite powers carrier₀ oc fk image₀ pred₀ closed currentSmall hξU₀ length diagram limit next constants ha ownerLocal
    obtain ⟨f, g, ff, graph, value⟩ := cover x B E pair hxE
    have image := coordinate m b₀ d₀ ha hn hnm code fb space dc₀ ft₀ rt₀ repr
    obtain ⟨F, _, hfF⟩ := embed.1.1.2.2 f (ff.mem_l I)
    exact ⟨b₀.val, y₀, f, a₁, F, fi.1.input_mem_of_pairMember image, ff, image, hfF,
      law f g E F ff graph value hfF⟩

  let C₀ := smdl_structure_l I (R := W) next.2.1
  let η : Env C₀ 0 := ⟨Fin.elim0, fun _ => ⟨w₁, newNumbers.member⟩⟩
  have ec := nextExt.native_l I next.2.1
  obtain ⟨pair, union⟩ := sc_pair_union_l ec η (targetTheory.algebra next.2.1 η)
  refine ⟨U, hu, nativeFinite, ⟨cU, R_U, mu, sourceTheory⟩,
    sourceSmall, l, H₂, D, u, common, targetSmall, commute, P, rankP, keep,
    κ₀, bκ, κ', hξκ, hξb, hκj, below, support, moved, support κ₀ below, ord₀, ord₁, ord₂, ord_fix, low_img, anchor_step,
    cD, R_D, cut, read, cutExt, cutAlgebra, cutFinite, cutTheory,
    (fun _ _ _ _ _ _ _ => rr_separation_l hZF hω mx theory next root hH₂ fi full atoms targetClosed),
    z, nextNumbers,
    (fun _ _ => nextNumbers.finite_function_l hZF (ZFC.models_zf_l cutTheory).1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l cutTheory))) (KP.exists_union (ZF.modelsKP (ZFC.models_zf_l cutTheory))) hω (fun _ h => h)), countable,
    w₀, w₁, z₀, z₁, hww₀, hww₁, omegaEdge, oldNumbers, newNumbers, oldGraph, newGraph, numeric, sequences, countableImage, ?_, representations, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a₀ ha
    obtain ⟨n, m, b₀, d₀, D₀, t₀, y₀, a₁, hn, hnm, code, fb, space, dc₀, ft₀, rt₀, hdy, repr, law, _, seed, bounded⟩ :=
      system.application_l hZF hω model ext parentTheory parentCollection nx hN U₀ w ξ ℓ e
        numbers finite powers carrier₀ oc fk image₀ pred₀ closed currentSmall hξU₀ length diagram limit next constants ha ownerLocal
    exact ⟨n, m, b₀, d₀, D₀, t₀, y₀, a₁, hn, hnm, code, fb, space, dc₀, ft₀, rt₀, hdy, repr,
      coordinate m b₀ d₀ ha hn hnm code fb space dc₀ ft₀ rt₀ repr, law, seed, bounded⟩
  · intro close ownerClose
    have hwH := (full w₁).mpr ⟨w.val, (dc w.val).mpr ⟨w.property, hwU⟩, hww₁⟩
    have uniform := targetCollection.uniform_l I (targetSmall w₁ newNumbers.member hwH)
    exact close.evaluation_l hZF hω (ZFC.dc_l I hZFC hω) model next embed ext oldNumbers newNumbers
      omegaEdge numeric uniform fi.1 (fun b a hba => (full a).mpr ⟨b, fi.1.input_mem_of_pairMember hba, hba⟩)
      representations (fun a fa bound => (countableImage ownerClose a fa bound).imp fun F hF => hF.2)

  · exact (sc_collapse_iff_l I hZF hω mx next root).mp
  · intro n a hn fa
    exact newNumbers.finite_function_l hZF ec pair union hω (fun _ h => h) hn fa
  · intro v t rootNumbers seq A hA
    obtain ⟨B, fs⟩ := ((sequences v t rootNumbers seq).2.2.2).space_l I hA
    obtain ⟨A₀, K₀, B₀, p₀, domain, space, carrier, bij, graph, _⟩ :=
      newNumbers.finite_codes_l hZF ec pair union hω (⟨A, hA⟩ : C₀.Domain) ⟨B, fs.mem_l⟩ fs
    exact ⟨B, A₀, K₀, B₀, p₀, fs, domain, space, carrier, bij, graph⟩
  · refine ⟨A', Q', Y', e', D₁, Γ₁, s, v, t, owned, nodes, carrier, sf, nativeGraph, vf,
      values, ft, res, hℓl, hUH, poolGraph, decode, b, H₁, hβb, hbH, image, pred, commute_full, ?_⟩
    intro n φ closed v w points
    let H₀ : C₀.Domain := ⟨H₁, embed.1.1.output_mem_of_pairMember hbH⟩
    have ht : C₀.TransitiveSet H₀ := by
      intro x hx y hy
      obtain ⟨a, _, hax⟩ := (image x.val).mp hx
      obtain ⟨b, _, hby⟩ := (pred a x.val hax y.val).mp hy
      exact (image y.val).mpr ⟨b, ft.1.input_mem_of_pairMember hby, hby⟩
    let nv : Nonempty {x : C₀.Domain // C₀.mem x H₀} :=
      ⟨⟨⟨l, ft.1.output_mem_of_pairMember hℓl⟩,
        (image l).mpr ⟨ℓ.val, ft.1.input_mem_of_pairMember hℓl, hℓl⟩⟩⟩
    exact rr_native_relative_l I nx next.2.1 Y' H₀ yt ht ⟨⟨ℓ, hℓY⟩⟩ nv
      carrier ft image pred φ closed v w points
  · let out : Prop :=
      ∃ K, Er_source_d I ω w₁ w₁ K C W ∧ It_source_d hZF ω o ∧
        ∀ α i T₀ Q₀ G₀ E₀ k₀ o₀, It_tree_d hZF ω c α T₀ Q₀ G₀ E₀ →
          M.SuccessorOf α i → Rd_entry_d i c₁ Q₀ → Rd_entry_d k₀ c' Q₀ → It_map_d G₀ o₀ k₀ q →
          ∃ β T₁ Q₁ G₁ E₁, It_tree_d hZF ω c β T₁ Q₁ G₁ E₁ ∧
            It_extension_d α i k₀ T₀ Q₀ G₀ E₀ β T₁ Q₁ G₁ E₁ ∧
            Rd_entry_d α o Q₁ ∧ It_map_d G₁ k₀ α j ∧ Rd_entry_d i p₀ E₁ ∧ It_map_d G₁ o₀ α q' ∧
            ∀ γ, It_lower_d I γ N S₀ ξ.val → It_critical_bound_d I γ Q₀ E₀ →
              It_critical_bound_d I γ Q₁ E₁
    change (∀ v t, Rr_layer_d I ω X R v t → Sc_sequences_d I v X R → Sc_collapse_d I X R → out) ∧
      (Zc_model_d I ω c X R → out)
    have build (K : M.Domain) (core : Er_source_d I ω w₁ w₁ K C W) : out := by
      have ready : It_source_d hZF ω o := ⟨hω, C, W, w₁, K, z₁, next, core, newNumbers⟩
      refine ⟨K, core, ready, ?_⟩
      intro α i T₀ Q₀ G₀ E₀ k₀ o₀ tree step owned parent origin
      obtain ⟨β, T₁, Q₁, G₁, E₁, nextTree, extension, node, edge, operation, compose⟩ :=
        it_apply_l hZF active tree step owned parent ready
      have square : It_comp_d q j q' := ⟨root.1.1.1.1, fun x E => (rootGraph x E).trans
        ⟨And.right, fun ⟨y, hxy, hyE⟩ => ⟨hq.1.1.input_mem_of_pairMember hxy, y, hxy, hyE⟩⟩⟩
      refine ⟨β, T₁, Q₁, G₁, E₁, nextTree, extension, node, edge, operation, compose o₀ q q' origin square, ?_⟩
      intro γ lower previous
      exact extension.critical_bound_l I previous
        (it_payload_bound_l I (ZF.modelsKP hZF) nextTree.move_function operation payload
          (extension.2.2.1 i _ owned) owner lower)

    constructor
    · intro v t rootNumbers seq collapse
      have nextSeq := (sequences v t rootNumbers seq).2.2.2
      obtain ⟨K, fs⟩ := nextSeq.space_l I newNumbers.member
      have hwH := (full w₁).mpr ⟨w.val, (dc w.val).mpr ⟨w.property, hwU⟩, hww₁⟩
      have core := Er_source_d.of_layer_l I (ZF.modelsKP hZF) hω nextExt newNumbers
        (targetSmall w₁ newNumbers.member hwH) fs targetTheory targetCollection nextSeq
        ((sc_collapse_iff_l I hZF hω mx next root).mp collapse)
      exact build K core
    · intro theory
      obtain ⟨K, core⟩ := (nextTheory theory).source_l hZF hω newNumbers
      exact build K core

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 极限共同秩段自动提供原后继工厂的闭包

回答和继续两条实际边共用此入口。从给定原模型自己的极限秩层构造
有限函数空间、乘积和子集闭包，再施加证书中的同一个扩展器。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.raw_rank_source_l {ω c₁ N S₀ : M.Domain}
    (hω : M.IsOmega ω) (nx : ∃ x, M.mem x N) :
    let N₀ := smdl_structure_l I (R := S₀) nx
    ∀ ground : N₀.Models ZFC,
    let hN := ZF.modelsKP (ZFC.models_zf_l ground)
    let J := kp_pair_l hN
    ∀ U₀ w ξ L F α β ζ X' K' R' δ cN dN N' T' jN θ : N₀.Domain,
    ∀ {c X R c' Y S q Γ H k z : M.Domain},
    Smdl_d I c₁ N S₀ → Zc_model_d I ω c X R → Smdl_d I c' Y S → Smap_d I ω c c' X Y q →
    Rr_layer_d I ω N S₀ w.val z → V_d J ζ U₀ → N₀.IsLimitOrdinal ζ →
    (∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U₀.val S₀) →
    M.IsSetInjectionFromTo I k Γ Y →
    (∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k) →
    (∀ x y, Rd_entry_d x y k → ∀ t, Rd_entry_d t y S ↔ ∃ d, Rd_entry_d d x S₀ ∧ Rd_entry_d d t k) →
    Rr_closed_d I Y S H → Rr_small_d I Y S H → N₀.mem β U₀ → N₀.mem ξ β →
    N₀.IsLimitOrdinal α → V_d J α β → N₀.mem α L →
    Ep_source_d J w ξ K' X' R' → V_d J δ X' → N₀.IsLimitOrdinal δ →
    Smem_d J cN X' R' → Smem_d J dN N' T' → It_ultra_d J w ξ L F cN dN jN →
    Sc_inaccessible_d w X' L → Ex_strength_d J w ξ L X' F →
    Rd_entry_d (M := N₀) ξ θ jN → N₀.MemberSubset L θ → It_local_d J w X' R' ξ L F →
    Er_rank_cut_d hZF ω c X R c' Y S q Γ k N S₀ z c₁ nx hN U₀ w ξ L F β X' K' jN := by
  intro N₀ ground hN J U₀ w ξ L F α β ζ X' K' R' δ cN dN N' T' jN θ
  intro c X R c' Y S q Γ H k z owner root model hq numbers rank₀ limit₀ carrier fk image pred closed small
    hβ hκ ha rankB hαL source rank height mx my ultra card strong critical bound loc
  have trans₀ := v_transitive_l J rank₀
  have hκ₀ := trans₀ β hβ ξ hκ
  have hw₀ := v_subset_mem_l J rank₀ hκ₀ source.below
  have algebra := sc_v_algebra_l ground limit₀ rank₀
  have finite : Fs_read_d (M := N₀) w U₀ := by
    refine ⟨trans₀, hw₀, algebra.pair, ?_, ?_⟩
    · exact fun m A f hm sub fn => sc_finite_function_l hN source.omega trans₀ algebra.pair algebra.union hw₀ sub hm fn
    · intro A m hA hm
      obtain ⟨D, space⟩ := ZF.exists_functionSpace (ZFC.models_zf_l ground) J m A
      obtain ⟨B, hB, mB, aB⟩ := v_joint_bound_l J rank₀ (trans₀ w hw₀ m hm) hA
      have hD : N₀.mem D U₀ := v_relations_mem_l J rank₀ limit₀ hB (fun f hf p hp => by
        have fn := (space f).mp hf
        obtain ⟨x, y, pair⟩ := fn.1.1 p hp
        exact ⟨x, mB x (fn.input_mem_of_pairMember ⟨p, pair, hp⟩),
          y, aB y (fn.output_mem_of_pairMember ⟨p, pair, hp⟩), pair⟩)
      exact ⟨D, hD, fun f => (space f).trans ⟨fn0_of_function_l hN, fn0_function_l hN⟩⟩
  have products (m d : N₀.Domain) (hm : N₀.mem m w) (space : Ep_space_d ξ m d) :
      ∃ P : N₀.Domain, N₀.mem P U₀ ∧ N₀.IsCartesianProduct J P d β := by
    obtain ⟨D, hD, ds⟩ := finite.spaces ξ m hκ₀ hm
    have eq := hN.1.eq_of_same_members D d (fun f => (ds f).trans (space f).symm)
    obtain ⟨P, prod⟩ := ZF.exists_cartesianProduct (ZFC.models_zf_l ground) J d β
    exact ⟨P, ZF.v_product_mem_l J (ZFC.models_zf_l ground) rank₀ limit₀ (eq ▸ hD) hβ prod, prod⟩
  have oc : Rr_closed_d I N S₀ U₀.val := by
    intro a b ha hb haU sub
    exact v_subset_mem_l J rank₀ (A := ⟨a, ha⟩) (B := ⟨b, hb⟩) haU (fun x hx => sub x.val x.property hx)
  have rule (ρ : Env N₀ 0) : Formula.satisfies ρ eo_kernel_m :=
    (Formula.closed_env_l eo_kernel_m eo_kernel_closed_l (funext fun i => Fin.elim0 i)).mp
      (eo_kernel_true_l ground ρ.free)
  exact loc.raw_rank_cut_l hZFC hω root.ext root.model (root.theory_l hZF hω) (root.collection_l hZF hω)
    model hq owner nx hN rule U₀ w ξ L F α β X' K' R' δ cN dN N' T' jN θ
    numbers finite products carrier oc fk image pred closed small hβ hκ source rank height
    mx my ultra card strong critical bound hαL ha rankB

/-- 扩展器施加到自身所属原模型时，实际秩切片的恒等图供应全部施加条件。 -/
theorem It_local_d.raw_self_l {ω c₁ N S₀ : M.Domain}
    (hω : M.IsOmega ω) (nx : ∃ x, M.mem x N) :
    let N₀ := smdl_structure_l I (R := S₀) nx
    ∀ ground : N₀.Models ZFC,
    let hN := ZF.modelsKP (ZFC.models_zf_l ground)
    let J := kp_pair_l hN
    ∀ w ξ L F α X' K' R' δ cN dN N' T' jN θ : N₀.Domain,
    ∀ {c X R q z : M.Domain},
    Smdl_d I c₁ N S₀ → Zc_model_d I ω c X R → Smap_d I ω c c₁ X N q →
    Rr_layer_d I ω N S₀ w.val z → V_d J δ X' → N₀.IsLimitOrdinal δ →
    N₀.IsLimitOrdinal α → N₀.mem ξ α → N₀.mem α L → N₀.mem L δ →
    Ep_source_d J w ξ K' X' R' → Smem_d J cN X' R' → Smem_d J dN N' T' →
    It_ultra_d J w ξ L F cN dN jN → Sc_inaccessible_d w X' L → Ex_strength_d J w ξ L X' F →
    Rd_entry_d (M := N₀) ξ θ jN → N₀.MemberSubset L θ → It_local_d J w X' R' ξ L F →
    ∃ β : N₀.Domain, ∃ Γ k,
      V_d J α β ∧ (∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x X'.val S₀) ∧
      (∀ x y, Rd_entry_d x y k ↔ M.mem x Γ ∧ x = y) ∧ Rr_small_d I N S₀ X'.val ∧
      Er_rank_cut_d hZF ω c X R c₁ N S₀ q Γ k N S₀ z c₁ nx hN X' w ξ L F β X' K' jN := by
  intro N₀ ground hN J w ξ L F α X' K' R' δ cN dN N' T' jN θ
  intro c X R q z owner root map numbers rank height ha hξ hαL hLδ source mx my ultra card strong crit bound loc
  have native := ZFC.models_zf_l ground
  obtain ⟨β,rankB⟩ := ZF.v_exists_l J native ha.1
  have hβ := ZF.v_mem_l J native rankB rank (height.1.transitive L hLδ α hαL)
  have hκ := ZF.v_ordinal_mem_l J native rankB hξ
  let ρ : Env M 2 := ⟨Fin.cases X'.val (fun _ => S₀),fun _ => N⟩
  let φ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨Γ,sep⟩ := ZF.separation_exists_d hZF φ ρ N
  have carrier x : M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x X'.val S₀ :=
    (sep x).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
  let ψ : BinarySchema 0 := { body := Formula.extensionalEq (.bound 1) .newest }
  let ε : Env M 0 := ⟨Fin.elim0,fun _ => N⟩
  have same x y : ψ.denote ε x y ↔ x = y := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  obtain ⟨k,fk,ks⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ ε
    (source := Γ) (target := N) (fun x _ => ⟨x,(same x x).mpr rfl⟩)
    (fun x _ y z hy hz => ((same x y).mp hy).symm.trans ((same x z).mp hz))
    (fun x y hx hy => (same x y).mp hy ▸ ((carrier x).mp hx).1)
  have graph x y : Rd_entry_d x y k ↔ M.mem x Γ ∧ x = y :=
    (ks x y).trans (and_congr_right fun _ => same x y)
  have inj : M.IsSetInjectionFromTo I k Γ N :=
    ⟨fk,fun x y v hx hy => ((graph x v).mp hx).2.trans ((graph y v).mp hy).2.symm⟩
  have image y : Rd_entry_d y X'.val S₀ ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k := by
    constructor
    · intro hy
      have hyΓ := (carrier y).mpr ⟨(owner.2.2.2 y X'.val hy).1,hy⟩
      exact ⟨y,hyΓ,(graph y y).mpr ⟨hyΓ,rfl⟩⟩
    · rintro ⟨x,hx,hxy⟩
      exact ((graph x y).mp hxy).2 ▸ ((carrier x).mp hx).2
  have pred x y (hxy : Rd_entry_d x y k) t :
      Rd_entry_d t y S₀ ↔ ∃ d, Rd_entry_d d x S₀ ∧ Rd_entry_d d t k := by
    obtain ⟨hx,rfl⟩ := (graph x y).mp hxy
    constructor
    · intro ht
      have htN := (owner.2.2.2 t x ht).1
      have htX := v_transitive_l J rank ⟨x,((carrier x).mp hx).1⟩ ((carrier x).mp hx).2 ⟨t,htN⟩ ht
      exact ⟨t,ht,(graph t t).mpr ⟨(carrier t).mpr ⟨htN,htX⟩,rfl⟩⟩
    · rintro ⟨d,hd,hdt⟩
      exact ((graph d t).mp hdt).2 ▸ hd
  have closed : Rr_closed_d I N S₀ X'.val := fun a b ha hb haX sub =>
    v_subset_mem_l J rank (A := ⟨a,ha⟩) (B := ⟨b,hb⟩) haX (fun x hx => sub x.val x.property hx)
  have small : Rr_small_d I N S₀ X'.val := by
    intro b hb _
    let b₀ : N₀.Domain := ⟨b,hb⟩
    obtain ⟨μ,f,ord,fn,onto⟩ := ZFC.ordinal_enum_l ground J b₀
    obtain ⟨g,inj,_⟩ := ZF.exists_rightInverseInjection_of_surjection_from_ordinal native J ord fn onto
    apply (rf_small_native_l I nx b₀).mpr
    simp only [sc_small_m,Formula.satisfies_exists_iff]
    exact ⟨μ,g,(sc_index_sat_l hN _ (.bound 1) (.bound 2) .newest).mpr
      (Sc_index_d.of_injection_l hN ord inj)⟩
  exact ⟨β,Γ,k,rankB,carrier,graph,small,loc.raw_rank_source_l hZFC hω nx ground
    X' w ξ L F α β δ X' K' R' δ cN dN N' T' jN θ owner root owner map numbers rank height
    carrier inj image pred closed small hβ hκ ha rankB hαL source rank height mx my ultra card strong crit bound⟩

end YesMetaZFC.SetTheory.LargeCardinal
