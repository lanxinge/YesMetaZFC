import YesMetaZFC.SetTheory.LargeCardinal.Extender.StrengthRank
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.SetTheory.LargeCardinal.Extender.UltraCertificate
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SystemRead
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.Model.SetTheory.Embedding.Relative
import YesMetaZFC.SetTheory.LargeCardinal.Extender.ReflectHull
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.StepSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Extender.LocalRead
import YesMetaZFC.SetTheory.LargeCardinal.Extender.StrengthAgreement
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.ActivityRead
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyHistory
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptCoordinates
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptMember
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptRank
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptLift
import YesMetaZFC.Model.SetTheory.Internal.RegularRankImage
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyNice
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyTree
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptRegular
import YesMetaZFC.SetTheory.CumulativeRegularCover
import YesMetaZFC.SetTheory.Card.FiniteParameters
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CutPull
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.InitialPull
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Descent

/-! # 所属短扩展器、不可达性和有限幂一致性的回拉

所属模型中的原公式沿实际限制反射；子集一致性只在有一侧隶属时取该子集
的初等像，因而无需假定壳包含所有背景子集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.pull_l {Ω ω ω' X R Y S c d σ κ κ' L L' F F' : M.Domain}
    (hΩ : M.IsOmega Ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S) (hs : Smap_d I Ω c d X Y σ)
    (hw : Rd_entry_d ω ω' σ) (hk : Rd_entry_d κ κ' σ) (hl : Rd_entry_d L L' σ) (hf : Rd_entry_d F F' σ)
    (loc : It_local_d I ω' Y S κ' L' F') : It_local_d I ω X R κ L F := by
  have owned {a b} (h : Rd_entry_d a b σ) := hs.1.1.input_mem_of_pairMember h
  obtain ⟨ωY, κY, LY, FY, loc⟩ := loc
  let ρ : Env (smdl_structure_l I (R := R) ⟨ω, owned hw⟩) 4 :=
    ⟨Fin.cases ⟨F, owned hf⟩ (Fin.cases ⟨L, owned hl⟩ (Fin.cases ⟨κ, owned hk⟩ (fun _ => ⟨ω, owned hw⟩))), fun _ => ⟨ω, owned hw⟩⟩
  let η : Env (smdl_structure_l I (R := S) ⟨ω', ωY⟩) 4 :=
    ⟨Fin.cases ⟨F', FY⟩ (Fin.cases ⟨L', LY⟩ (Fin.cases ⟨κ', κY⟩ (fun _ => ⟨ω', ωY⟩))), fun _ => ⟨ω', ωY⟩⟩
  let φ : Formula 1 4 := ex_short_m (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  have tr := smap_source_l I hZF hΩ mx my hs φ (by simp -implicitDefEqProofs [φ])
    ⟨ρ.bound, ρ.free⟩ ⟨η.bound, η.free⟩ (Fin.cases hf (Fin.cases hl (Fin.cases hk (fun _ => hw))))
  exact ⟨owned hw, owned hk, owned hl, owned hf, tr.mpr loc⟩

theorem _root_.YesMetaZFC.SetTheory.Internal.Sc_inaccessible_d.pull_l
    {ω X R Y S c d σ κ κ' : M.Domain} (hω : M.IsOmega ω)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (hs : Smap_d I ω c d X Y σ)
    (hw : Rd_entry_d ω ω σ) (hk : Rd_entry_d κ κ' σ)
    (big : Sc_inaccessible_d ω Y κ') : Sc_inaccessible_d ω X κ := by
  have hωX := hs.1.1.input_mem_of_pairMember hw
  have hκX := hs.1.1.input_mem_of_pairMember hk
  obtain ⟨hωY, hκY, h⟩ := big
  let ρ : Env (rt_model_l X ⟨⟨ω, hωX⟩⟩) 2 := ⟨Fin.cases ⟨κ, hκX⟩ (fun _ => ⟨ω, hωX⟩), fun _ => ⟨ω, hωX⟩⟩
  let η : Env (rt_model_l Y ⟨⟨ω, hωY⟩⟩) 2 := ⟨Fin.cases ⟨κ', hκY⟩ (fun _ => ⟨ω, hωY⟩), fun _ => ⟨ω, hωY⟩⟩
  let φ : Formula 1 2 := sc_inaccessible_m (.bound 1) .newest
  have tr := smap_source_l I hZF hω mx.1 my.1 hs φ (by simp -implicitDefEqProofs [φ])
    ⟨ρ.bound, ρ.free⟩ ⟨η.bound, η.free⟩ (Fin.cases hk (fun _ => hw))
  exact ⟨hωX, hκX, (smem_formula_l I mx _ φ ρ).mpr (tr.mpr ((smem_formula_l I my _ φ η).mp h))⟩

theorem Ea_agree_d.pull_l {ω B R b U S u π κ κ' X X' Y Y' : M.Domain}
    (hω : M.IsOmega ω) (ambient : Fs_read_d ω B) (target : Fs_read_d ω U)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (hk : Rd_entry_d κ κ' π) (hx : Rd_entry_d X X' π) (hy : Rd_entry_d Y Y' π)
    (big : Ea_agree_d ω κ' X' Y') : Ea_agree_d ω κ X Y := by
  have bt := ambient.transitive
  have ut := target.transitive
  intro n D A hn hd sub
  obtain ⟨D₀, hD, space⟩ := ambient.spaces κ n (hj.1.1.input_mem_of_pairMember hk) hn
  have eq := hZF.1.eq_of_same_members D₀ D (fun f => (space f).trans (hd f).symm)
  subst D₀
  obtain ⟨D', hD', hDD⟩ := hj.1.1.2.2 D hD
  have nat := hj.natural_l hZF hω bt ut mb mu ambient.omega_mem n hn
  have tr := hj.forall_delta_l hZF hω bt ut mb mu
    (.iff (.mem (.newest : Term 4) (.bound 1)) (fn0_m (.bound 3) (.bound 2) .newest))
    (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]) (.iff (.mem ..) (fn0_delta_l ..))
    ⟨Fin.cases D (Fin.cases κ (fun _ => n)), fun _ => n⟩
    ⟨Fin.cases D' (Fin.cases κ' (fun _ => n)), fun _ => n⟩ (Fin.cases hDD (Fin.cases hk (fun _ => nat)))
  simp only [Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, fn0_sat_l hZF.1] at tr
  have values := tr.mp (fun f _ => hd f)
  have hd' : Ep_space_d κ' n D' := fun f => ⟨fun hf => (values f (ut D' hD' f hf)).mp hf,
    fun hf => (values f (target.functions n κ' f hn (ut κ' (hj.1.1.output_mem_of_pairMember hk)) hf)).mpr hf⟩
  have read (owned : M.mem A B) : M.mem A X ↔ M.mem A Y := by
    obtain ⟨A', _, hAA⟩ := hj.1.1.2.2 A owned
    have agree := big n D' A' hn hd' ((hj.subset_l hZF hω bt ut mb mu hAA hDD).mp sub)
    exact (hj.member_l I hZF hω mb mu hAA hx).trans (agree.trans (hj.member_l I hZF hω mb mu hAA hy).symm)
  exact ⟨fun h => (read (bt X (hj.1.1.input_mem_of_pairMember hx) A h)).mp h,
    fun h => (read (bt Y (hj.1.1.input_mem_of_pairMember hy) A h)).mpr h⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 初等图回拉部分列

支撑列在恒等步处没有值。回拉只反射已有条目，不能给空操作填造支撑。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.partial_column_l {ω B R b U S u π C V f g : M.Domain}
    (hω : M.IsOmega ω) (bt : M.TransitiveSet B) (ut : M.TransitiveSet U) (vt : M.TransitiveSet V)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (hCV : Rd_entry_d C V π) (hw : Rd_entry_d ω ω π) (hfg : Rd_entry_d f g π)
    (hf : M.mem f C) (gf : M.IsSetFunction I g) (bound : ∀ i x, Rd_entry_d i x g → M.mem i ω) :
    M.IsSetFunction I f ∧ ∀ i x, Rd_entry_d i x f → M.mem i ω ∧ M.mem x C := by
  let φ : Formula 1 3 := set[3] ⟪∀ p ∈ ⌜(Term.newest : Term 3)⌝ₛ,
    ∃ i ∈ ⌜(Term.bound 2 : Term 3)⌝ₛ, ∃ x ∈ ⌜(Term.bound 1 : Term 3)⌝ₛ, ⌜kpair0_m⌝ₚ(p, i, x)⟫
  have tr := smap_delta_l I hZF hω bt ut mb mu hj φ (by simp -implicitDefEqProofs [φ])
    (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..))))
    ⟨Fin.cases f (Fin.cases C (fun _ => ω)), fun _ => ω⟩
    ⟨Fin.cases g (Fin.cases V (fun _ => ω)), fun _ => ω⟩ (Fin.cases hfg (Fin.cases hCV (fun _ => hw)))
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1] at tr
  have shape := tr.mpr (fun p hp => by
    obtain ⟨i, x, pair⟩ := gf.1 p hp
    have hx := rd_entry_transitive_l vt ((hj.member_l I hZF hω mb mu hfg hCV).mp hf) ⟨p, pair, hp⟩
    exact ⟨i, bound i x ⟨p, pair, hp⟩, x, hx.2, pair⟩)
  have bd i x (h : Rd_entry_d i x f) : M.mem i ω ∧ M.mem x C := by
    obtain ⟨p, pair, hp⟩ := h
    obtain ⟨i', hi, x', hx, pair'⟩ := shape p hp
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair' pair
    exact ⟨hi, hx⟩
  refine ⟨⟨fun p hp => by obtain ⟨i, _, x, _, pair⟩ := shape p hp; exact ⟨i, x, pair⟩, ?_⟩, bd⟩
  intro i x y hx hy
  have hB := hj.1.1.input_mem_of_pairMember hfg
  obtain ⟨i', _, hi'⟩ := hj.1.1.2.2 i (rd_entry_transitive_l bt hB hx).1
  obtain ⟨x', _, hx'⟩ := hj.1.1.2.2 x (rd_entry_transitive_l bt hB hx).2
  obtain ⟨y', _, hy'⟩ := hj.1.1.2.2 y (rd_entry_transitive_l bt hB hy).2
  have eq := gf.2 i' x' y' ((hj.entry_l hZF hω bt ut mb mu hi' hx' hfg).mp hx)
    ((hj.entry_l hZF hω bt ut mb mu hi' hy' hfg).mp hy)
  exact hj.1.2 x y y' (eq ▸ hx') hy'

theorem Smap_d.partial_entry_preimage_l {ω B R b U S u π C V f g i i' y : M.Domain}
    (hω : M.IsOmega ω) (bt : M.TransitiveSet B) (ut : M.TransitiveSet U) (vt : M.TransitiveSet V)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (hCV : Rd_entry_d C V π) (hf : M.mem f C) (gf : M.IsSetFunction I g)
    (hfg : Rd_entry_d f g π) (hi : Rd_entry_d i i' π) (hy : Rd_entry_d i' y g) :
    ∃ x, M.mem x C ∧ Rd_entry_d i x f ∧ Rd_entry_d x y π := by
  have tr := hj.exists_delta_l hZF hω bt ut mb mu
    (.conj (.mem (.newest : Term 4) (.bound 3)) (rd_entry0_m (.bound 2) .newest (.bound 1)))
    (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]) (.conj (.mem ..) (rd_entry0_delta_l ..))
    ⟨Fin.cases f (Fin.cases i (fun _ => C)), fun _ => C⟩
    ⟨Fin.cases g (Fin.cases i' (fun _ => V)), fun _ => V⟩ (Fin.cases hfg (Fin.cases hi (fun _ => hCV)))
  simp only [Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, rd_entry0_sat_l hZF.1] at tr
  have hyU := (rd_entry_transitive_l ut (hj.1.1.output_mem_of_pairMember hfg) hy).2
  have hyV := (rd_entry_transitive_l vt ((hj.member_l I hZF hω mb mu hfg hCV).mp hf) hy).2
  obtain ⟨x, hxB, hxC, hix⟩ := tr.mpr ⟨y, hyU, hyV, hy⟩
  obtain ⟨z, _, hxz⟩ := hj.1.1.2.2 x hxB
  exact ⟨x, hxC, hix, gf.2 i' z y ((hj.entry_l hZF hω bt ut mb mu hi hxz hfg).mp hix) hy ▸ hxz⟩

end YesMetaZFC.SetTheory.Internal

/-! ## Skolem 回拉后指定超幂边的完整恢复

相对证书提供原商、原常值函数、原坍塌和原复合方块。有限闭性恢复全部
代表，随后由实际源的 Łoś 定理证明完整初等性，不假定满足关系绝对。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

private theorem rt_it_comp_l (hKP : M.Models KP) {V : M.Domain} (hv : M.TransitiveSet V)
    (nv : Nonempty {x // M.mem x V})
    (pair : ∀ a b, M.mem a V → M.mem b V → ∃ p, M.mem p V ∧ Pair_d M p a b)
    (f g j : (rt_model_l V nv).Domain) (h : It_comp_d f g j) : It_comp_d f.val g.val j.val := by
  have ent := rt_entry_l hv nv hKP.1
  refine ⟨(rt_relation_l hKP.1 (KP.exists_pair hKP) hv nv pair j).mp h.1, fun x z => ⟨?_, ?_⟩⟩
  · intro hxz
    have xz := rd_entry_transitive_l hv j.property hxz
    obtain ⟨y, hxy, hyz⟩ := (h.2 ⟨x, xz.1⟩ ⟨z, xz.2⟩).mp ((ent ..).mpr hxz)
    exact ⟨y.val, (ent ..).mp hxy, (ent ..).mp hyz⟩
  · rintro ⟨y, hxy, hyz⟩
    have xy := rd_entry_transitive_l hv f.property hxy
    have yz := rd_entry_transitive_l hv g.property hyz
    exact (ent ..).mp ((h.2 ⟨x, xy.1⟩ ⟨z, yz.2⟩).mpr ⟨⟨y, xy.2⟩, (ent ..).mpr hxy, (ent ..).mpr hyz⟩)

private theorem rt_ep_constants_l (hKP : M.Models KP) {V : M.Domain} (hv : M.TransitiveSet V)
    (nv : Nonempty {x // M.mem x V})
    (pair : ∀ a b, M.mem a V → M.mem b V → ∃ p, M.mem p V ∧ Pair_d M p a b)
    (X q i : (rt_model_l V nv).Domain) (h : Ep_constants_d X q i) : Ep_constants_d X.val q.val i.val := by
  have ent := rt_entry_l hv nv hKP.1
  intro x E hxE
  have xe := rd_entry_transitive_l hv i.property hxE
  obtain ⟨u, a, B, f, D, hd, ⟨hf, C, hc, fn⟩, constant, hfb, hp, huE⟩ :=
    h ⟨x, xe.1⟩ ⟨E, xe.2⟩ ((ent ..).mpr hxE)
  exact ⟨u.val, a.val, B.val, f.val, D.val, hd, ⟨hf, C.val, hc, (rt_fn_l hv nv hKP.1 ..).mp fn⟩,
    fun v hvD => (ent ..).mp (constant ⟨v, hv D.val D.property v hvD⟩ hvD), hfb,
    (rt_kpair_l hKP.1 (KP.exists_pair hKP) hv nv pair ..).mp hp, (ent ..).mp huE⟩

theorem it_ultra_read_l (hZFC : M.Models ZFC) {ω V X R K' : M.Domain}
    (ambient : Fs_read_d ω V) (nv : Nonempty {x // M.mem x V})
    {n} (η : Env (rt_model_l V nv) n) (w μ L F c d j : Term n) (hw : (w.eval η).val = ω)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω (μ.eval η).val K' X R)
    (mx : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) (c.eval η).val X R)
    (family : Em_source_d ω (μ.eval η).val (L.eval η).val X (F.eval η).val)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC)))
      ω (μ.eval η).val (L.eval η).val X (F.eval η).val)
    (h : Formula.satisfies η (it_ultra_m w μ L F c d j)) :
    It_ultra_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω (μ.eval η).val (L.eval η).val (F.eval η).val
      (c.eval η).val (d.eval η).val (j.eval η).val := by
  let hZF := ZFC.models_zf_l hZFC
  let J := rt_pair_l ambient.transitive nv hZF.1 ambient.pair
  have ext := rt_model_ext_l hZF.1 ambient.transitive nv
  simp only [it_ultra_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    smem_sat_l J, ep_system_sat_l J ext, di_limit_sat_l ext, smdl_sat_l J, wc_graph_sat_l ext,
    Formula.satisfies_isBijectionFromTo_iff J ext, smap_sat_l J ext, ep_constants_sat_l ext,
    it_comp_sat_l ext, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at h
  obtain ⟨x, r, y, s, O, P, Z, A, p, T, U, q, b, C, S, i, e,
    hx, hy, system, limit, model, collapse, bij, _, hi, constants, _, comp⟩ := h
  have hx := (rt_smem_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ambient.transitive nv ambient.pair ..).mp hx
  have hy := (rt_smem_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ambient.transitive nv ambient.pair ..).mp hy
  obtain ⟨eqx, eqr⟩ := smdl_unique_l (kp_pair_l (ZF.modelsKP hZF)) hx.1 mx.1
  have source' : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω (μ.eval η).val K' x.val r.val := by simpa only [eqx, eqr] using source
  have family' : Em_source_d ω (μ.eval η).val (L.eval η).val x.val (F.eval η).val := by simpa only [eqx] using family
  have coherent' : Ec_source_d (kp_pair_l (ZF.modelsKP hZF)) ω (μ.eval η).val (L.eval η).val x.val (F.eval η).val := by
    simpa only [eqx] using coherent
  exact it_ultra_of_certificate_l hZFC source' family' coherent' hx hy
    (ambient.system_read_l hZF nv (w.eval η) (μ.eval η) (L.eval η) x r (F.eval η) O P Z A p T U hw system)
    (rt_di_limit_l (ZF.modelsKP hZF) ambient.transitive nv ambient.pair A p T U q C S limit)
    ((rt_smdl_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ambient.transitive nv ambient.pair ..).mp model)
    (rt_wc_graph_l (ZF.modelsKP hZF) ambient.transitive nv ambient.pair C S e collapse)
    ((rt_bijection_l ambient.transitive nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ambient.pair ..).mp bij)
    (fn0_of_function_l (ZF.modelsKP hZF)
      ((rt_function_from_l ambient.transitive nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ambient.pair ..).mp hi.1.1))
    (rt_ep_constants_l (ZF.modelsKP hZF) ambient.transitive nv ambient.pair x q i constants)
    (rt_it_comp_l (ZF.modelsKP hZF) ambient.transitive nv ambient.pair i e (j.eval η) comp)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 反射壳中原指定超幂边的回拉

大树的真实超幂证书先由有限反射进入证书层，再沿外层初等图进入小层。
读取原商及塌缩后，Łoś 定理恢复同一张小边的完整证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_ultra_pull_l {ω B R b U S u C V π X P K : M.Domain}
    (bt : M.TransitiveSet B) (ut : M.TransitiveSet U)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (ambient : Fs_read_d ω C) (nc : Nonempty {x // M.mem x C}) (hCV : Rd_entry_d C V π)
    (reflect : Lr_reflect_d (it_ultra_m (d := 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)) V)
    (ρ : Env (rt_model_l C nc) 7) (η : Env M 7) (hw : (ρ.bound 6).val = ω)
    (images : ∀ i, Rd_entry_d (ρ.bound i).val (η.bound i) π)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω (ρ.bound 5).val K X P) (mx : Smem_d I (ρ.bound 2).val X P)
    (family : Em_source_d ω (ρ.bound 5).val (ρ.bound 4).val X (ρ.bound 3).val)
    (coherent : Ec_source_d I ω (ρ.bound 5).val (ρ.bound 4).val X (ρ.bound 3).val)
    (big : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) (η.bound 6) (η.bound 5) (η.bound 4) (η.bound 3) (η.bound 2) (η.bound 1) (η.bound 0)) :
    It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω (ρ.bound 5).val (ρ.bound 4).val (ρ.bound 3).val (ρ.bound 2).val (ρ.bound 1).val (ρ.bound 0).val := by
  have tr := hj.reflected_l hZF source.omega bt ut mb mu ambient.transitive nc hCV
    (it_ultra_m (d := 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0))
    (by simp -implicitDefEqProofs) reflect ρ η images
  exact it_ultra_read_l hZFC ambient nc ρ (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
    hw source mx family coherent (tr.mpr ((it_ultra_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1 η ..).mpr big))

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 保留原树序的可数模型列及全初等边列

指定有限参数一并放入种子；原树序逐点固定。证书层同时反射原超幂公式，
供同一小树的操作列继续读取指定商和塌缩。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_diagram_hull_l {ω T Q G : M.Domain} (hω : M.IsOmega ω)
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G) (sources : ∀ i c, Rd_entry_d i c Q → It_source_d hZF ω c)
    {n} (v : Fin n → M.Domain) : ∃ B R b K U S u J C V π Q₀ G₀,
      Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω K B R ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω J U S ∧ Smem_d I b B R ∧ Smem_d I u U S ∧
      Smap_d I ω b u B U π ∧ M.CardinalLessOrEqual I B ω ∧ M.mem C B ∧ Fs_read_d ω C ∧ M.TransitiveSet V ∧
      Rd_entry_d C V π ∧ M.mem T C ∧ M.mem Q₀ C ∧ M.mem G₀ C ∧
      Rd_entry_d T T π ∧ Rd_entry_d Q₀ Q π ∧ Rd_entry_d G₀ G π ∧
      It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q₀ G₀ ∧ (∀ i c, Rd_entry_d i c Q₀ → It_source_d hZF ω c) ∧
      Lr_reflect_d (it_ultra_m (d := 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)) V ∧
      ∀ i, ∃ x, M.mem x C ∧ Rd_entry_d x (v i) π := by
  let w : Fin (n + 3) → M.Domain := Fin.cases T (Fin.cases Q (Fin.cases G v))
  obtain ⟨B, R, b, K, U, S, u, J, C, V, π, sb, su, mb, mu, hj, count, hC, fs, vt, hCV, reflect, params⟩ :=
    ep_reflect_hull_l hZFC hω w
      (it_ultra_m (d := 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0))
      (by simp -implicitDefEqProofs)
  obtain ⟨T₀, hT, hTT⟩ := params 0
  obtain ⟨Q₀, hQ, hQQ⟩ := params 1
  obtain ⟨G₀, hG, hGG⟩ := params 2
  obtain ⟨eq, small, ready⟩ := it_diagram_pull_l hZF sb su mb mu hj hC fs.transitive vt hCV hQ hG hTT hQQ hGG diagram sources
  change T₀ = T at eq
  subst T₀
  exact ⟨B, R, b, K, U, S, u, J, C, V, π, Q₀, G₀, sb, su, mb, mu, hj, count, hC, fs, vt, hCV,
    hT, hQ, hG, hTT, hQQ, hGG, small, ready, reflect, fun i => params i.succ.succ.succ⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原 nice 树沿反射壳整体回拉

全初等边列先已恢复；所属判断和最大强度分别由模型限制与有界证书反射。
每条指定超幂使用原公式的有限反射，商、塌缩和边图均保持原值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_pnice_pull_l {ω B R b K U S u J C V π c c' T Q Q' G G' E E' L L' : M.Domain}
    (sb : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω K B R) (su : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω J U S)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (hC : M.mem C B) (fs : Fs_read_d ω C) (vt : M.TransitiveSet V) (hCV : Rd_entry_d C V π)
    (hQ : M.mem Q C) (hG : M.mem G C) (hE : M.mem E C) (hL : M.mem L C)
    (hcc : Rd_entry_d c c' π) (hTT : Rd_entry_d T T π) (hQQ : Rd_entry_d Q Q' π)
    (hGG : Rd_entry_d G G' π) (hEE : Rd_entry_d E E' π) (hLL : Rd_entry_d L L' π)
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G) (big : It_pnice_d hZF ω c' ω T Q' G' E' L')
    (models : ∀ i a, Rd_entry_d i a Q' → It_mem_d I a)
    (powers : ∀ i a Y W, Rd_entry_d i a Q' → Smem_d I a Y W → Sc_power_d Y)
    (reflect : Lr_reflect_d (it_ultra_m (d := 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)) V) :
    It_pnice_d hZF ω c ω T Q G E L := by
  have actual i a (ha : Rd_entry_d i a Q') := (big.tree.sources i a ha).mem_l hZF (models i a ha)
  have hw := sb.omega
  have cb := sb.transitive C hC
  have nat := hj.natural_l hZF hw sb.transitive su.transitive mb mu sb.omega_mem
  have omega := hj.omega_l I hZF hw sb.transitive su.transitive mb mu sb.omega_mem
  -- 内部 ω 上的每一步都有操作；因此操作列及支撑列均保持完整定义域。
  have ed i : (∃ p, Rd_entry_d i p E') ↔ M.mem i ω := (big.tree.move_domain i).trans
    ⟨fun ⟨j, hj, sj⟩ => hw.transitive (ZF.modelsKP hZF) j hj i sj.predecessor_mem,
      fun hi => (hw.1.2 i hi).imp fun j h => ⟨h.2, h.1⟩⟩
  have qf := hj.column_l hZF hw sb.transitive su.transitive vt mb mu hCV omega hQQ hQ
    big.tree.diagram.model_function big.tree.diagram.model_domain
  have gf := hj.column_l hZF hw sb.transitive su.transitive vt mb mu hCV hTT hGG hG
    big.tree.diagram.map_function big.tree.diagram.map_domain
  have ef := hj.column_l hZF hw sb.transitive su.transitive vt mb mu hCV omega hEE hE big.tree.move_function (fun i => (ed i).symm)
  have lf := hj.partial_column_l hZF hw sb.transitive su.transitive vt mb mu hCV omega hLL hL big.function (by
    intro i ρ hρ
    obtain ⟨p, _, _, hp, _⟩ := (big.levels i ρ).mp hρ
    exact (ed i).mp ⟨p, hp⟩)
  have imageL {i ρ} (hρ : Rd_entry_d i ρ L) : ∃ ρ', Rd_entry_d i ρ' L' ∧ Rd_entry_d ρ ρ' π := by
    obtain ⟨ρ', _, hρρ⟩ := hj.1.1.2.2 ρ (cb ρ (lf.2 i ρ hρ).2)
    exact ⟨ρ', (hj.entry_l hZF hw sb.transitive su.transitive mb mu (nat i (lf.2 i ρ hρ).1) hρρ hLL).mp hρ, hρρ⟩
  have read {D f g i i' y} (ff : Fn0_d D C f) (gg : M.IsSetFunction I g) (hfg : Rd_entry_d f g π)
      (hi : Rd_entry_d i i' π) (hiD : M.mem i D) (hy : Rd_entry_d i' y g) :=
    hj.entry_preimage_l hZF hw sb.transitive su.transitive mb mu cb ff gg hfg hi hiD hy
  have image {f g i p} (ff : Fn0_d ω C f) (hfg : Rd_entry_d f g π) (hp : Rd_entry_d i p f) :
      ∃ p', Rd_entry_d i p' g ∧ Rd_entry_d p p' π := by
    obtain ⟨p', _, hpp⟩ := hj.1.1.2.2 p (cb p (ff.bound_l hp).2)
    exact ⟨p', (hj.entry_l hZF hw sb.transitive su.transitive mb mu (nat i (ff.bound_l hp).1) hpp hfg).mp hp, hpp⟩
  have payload {p p' κ ρ F} (hpp : Rd_entry_d p p' π) (pay : It_payload_d p κ ρ F) :
      ∃ κ' ρ' F', It_payload_d p' κ' ρ' F' ∧ Rd_entry_d κ κ' π ∧ Rd_entry_d ρ ρ' π ∧ Rd_entry_d F F' π := by
    obtain ⟨r, pr, rf⟩ := pay
    have kr := pr.mem_l M sb.transitive (hj.1.1.input_mem_of_pairMember hpp)
    have lf := rf.mem_l M sb.transitive kr.2
    obtain ⟨κ', _, hk⟩ := hj.1.1.2.2 κ kr.1
    obtain ⟨r', _, hr⟩ := hj.1.1.2.2 r kr.2
    obtain ⟨ρ', _, hl⟩ := hj.1.1.2.2 ρ lf.1
    obtain ⟨F', _, hf⟩ := hj.1.1.2.2 F lf.2
    exact ⟨κ', ρ', F', ⟨r', (hj.kpair_l hZF hw sb.transitive su.transitive mb mu hpp hk hr).mp pr,
      (hj.kpair_l hZF hw sb.transitive su.transitive mb mu hr hl hf).mp rf⟩, hk, hl, hf⟩
  have model {i a a' Y W} (ha : Rd_entry_d i a' Q') (haa : Rd_entry_d a a' π) (my : Smem_d I a' Y W) :
      ∃ X P H σ, Smem_d I a X P ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω H X P ∧ Rd_entry_d X Y π ∧
        M.IsRestrictionOf I σ π X ∧ Smap_d I ω a a' X Y σ ∧ Sc_power_d X := by
    obtain ⟨Y₀, W₀, N, my₀, sy⟩ := actual i a' ha
    obtain ⟨ey, ew⟩ := smdl_unique_l I my₀.1 my.1
    subst Y₀ W₀
    obtain ⟨X, P, H, σ, mx, sx, hXY, res, hs⟩ := ep_set_source_pull_l hZF sb su mb mu hj haa my sy
    exact ⟨X, P, H, σ, mx, sx, hXY, res, hs,
      (sc_power_iff_l hZF hw sx.transitive sy.transitive mx my hs).mpr (powers i a' Y W ha my)⟩
  have sources i a (ha : Rd_entry_d i a Q) : It_source_d hZF ω a := by
    obtain ⟨a', ha', haa⟩ := image qf hQQ ha
    obtain ⟨Y, W, _, my, _⟩ := actual i a' ha'
    obtain ⟨X, P, H, _, mx, sx, _⟩ := model ha' haa my
    exact it_source_mem_l hZF mx sx
  refine ⟨{
      omega := hw
      diagram := diagram
      root := ?_
      move_function := (fn0_function_l (ZF.modelsKP hZF) ef).1
      move_domain := ?_
      steps := ?_
      limits := ?_
      sources := sources },
    lf.1, ?_, ?_, ?_⟩
  · intro o ho
    have hoω := (big.tree.diagram.model_domain o).mpr ⟨c', big.tree.root o ho⟩
    obtain ⟨a, _, ha, haa⟩ := read qf big.tree.diagram.model_function hQQ (nat o hoω) hoω (big.tree.root o ho)
    exact (hj.1.2 a c c' haa hcc) ▸ ha
  · intro i
    exact ((fn0_function_l (ZF.modelsKP hZF) ef).2.1 i).symm.trans ((ed i).symm.trans (big.tree.move_domain i))
  · intro i j hjω succ
    -- 读取原前驱及各列中的指定条目，保持原树边与超幂。
    have hi := hw.transitive (ZF.modelsKP hZF) j hjω i succ.predecessor_mem
    obtain ⟨k, a', d', b', g', p', pred, ha', hd', hb', hg', hp', step⟩ := big.tree.steps i j hjω succ
    have hk := hw.transitive (ZF.modelsKP hZF) j hjω k pred.1
    obtain ⟨a, _, ha, haa⟩ := read qf big.tree.diagram.model_function hQQ (nat i hi) hi ha'
    obtain ⟨d, hdC, hd, hdd⟩ := read qf big.tree.diagram.model_function hQQ (nat k hk) hk hd'
    obtain ⟨e, heC, he, hee⟩ := read qf big.tree.diagram.model_function hQQ (nat j hjω) hjω hb'
    obtain ⟨p, hpC, hp, hpp⟩ := read ef big.tree.move_function hEE (nat i hi) hi hp'
    obtain ⟨r, pair, hr⟩ := hg'
    have hrT := (big.tree.diagram.map_domain r).mpr ⟨g', hr⟩
    have fixed := hj.fixed_pair_l hZF hw sb.transitive su.transitive mb mu
      (sb.transitive T (hj.1.1.input_mem_of_pairMember hTT) r hrT) pair (nat k hk) (nat j hjω)
    obtain ⟨g, hgC, hg, hgg⟩ := read gf big.tree.diagram.map_function hGG fixed hrT hr
    rcases step with ⟨empty, eq, codes, ident⟩ | active
    · have empty₀ x (hx : M.mem x p) : False := by
        obtain ⟨x', _, hxx⟩ := hj.1.1.2.2 x (sb.transitive p (hj.1.1.input_mem_of_pairMember hpp) x hx)
        exact empty x' ((hj.member_l I hZF hw mb mu hxx hpp).mp hx)
      have codes₀ : e = a := hj.1.2 e a a' (codes ▸ hee) haa
      have ident₀ x y (hxy : Rd_entry_d x y g) : x = y := by
        have xy := rd_entry_transitive_l sb.transitive (cb g hgC) hxy
        obtain ⟨x', _, hxx⟩ := hj.1.1.2.2 x xy.1
        obtain ⟨y', _, hyy⟩ := hj.1.1.2.2 y xy.2
        have equal := ident x' y' ((hj.entry_l hZF hw sb.transitive su.transitive mb mu hxx hyy hgg).mp hxy)
        exact hj.1.2 x y y' (equal ▸ hxx) hyy
      exact ⟨k, a, d, e, g, p, pred, ha, hd, he, ⟨r, pair, hg⟩, hp, Or.inl ⟨empty₀, eq, codes₀, ident₀⟩⟩
    have data := active
    obtain ⟨κ',ρ',F',Y,W,Z,H,pay',my',mz',_⟩ := data
    obtain ⟨Y₀,W₀,KY,my,sy⟩ := actual i a' ha'
    obtain ⟨eqY,eqW⟩ := smdl_unique_l I my.1 my'
    subst Y₀ W₀
    obtain ⟨Z₀,H₀,KZ,mz,sz⟩ := actual k d' hd'
    obtain ⟨eqZ,eqH⟩ := smdl_unique_l I mz.1 mz'
    subst Z₀ H₀
    obtain ⟨V₀,R₀,KV,mt,st⟩ := actual j b' hb'
    obtain ⟨loc',agree',ultra'⟩ := It_active_d.read_l hZF sy sz my mz mt st.transitive pay' active
    obtain ⟨κ, ρ, F, pay, hκ, hρ, hF⟩ := it_payload_pull_l hZF hw sb.transitive su.transitive mb mu hj hpp pay'
    obtain ⟨X, P, K₀, σ, mx, sx, hXY, res, hs, power⟩ := model ha' haa my
    obtain ⟨N, O, K₁, τ, mn, sn, hNZ, _, _, _⟩ := model hd' hdd mz
    have lift {x y} (hxy : Rd_entry_d x y π) (hy : M.mem y Y) :=
      (res.2 x y).mpr ⟨(hj.member_l I hZF hw mb mu hxy hXY).mpr hy, hxy⟩
    have loc := loc'.pull_l hZF hw mx.1 my.1 hs (lift omega loc'.1) (lift hκ loc'.2.1)
      (lift hρ loc'.2.2.1) (lift hF loc'.2.2.2.1)
    have agree := agree'.pull_l hZF hw (sb.read_source_l hZF) (su.read_source_l hZF) mb mu hj hκ hXY hNZ
    have ko := (loc.ordinals_l (ZF.modelsKP hZF) sx.transitive sx.code).1
    obtain ⟨K₂, owner⟩ := sx.rebase_l loc.2.1
      (by obtain ⟨_, _, _, _, pre⟩ := (it_local_mem_l I sx.code).mp loc
          simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
          exact ko.transitive ω pre.1.2.2.1)
      (sc_ordinal_small_l hZF hw sx.transitive mx sx.theory loc.2.1 ko)
    obtain ⟨K₃, parent⟩ := agree.subset_l.alphabet_l hZF owner sn ko
    obtain ⟨P₀, hP₀, pool⟩ := power K₂ owner.finite.mem_l
    have family := (loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
      (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory (owner.finite_l (ZF.modelsKP hZF)) hP₀ pool)).transfer_l agree
    have coherent := (loc.coherent_l hZF (owner.read_source_l hZF) owner.code).transfer_l hZF agree
    -- 真实有限幂一致性给出小施加源的族与相干性，再读取原超幂证书。
    obtain ⟨t, pt, tf⟩ := pay
    have kp := pt.mem_l M fs.transitive hpC
    have lp := tf.mem_l M fs.transitive kp.2
    let nc : Nonempty {x // M.mem x C} := ⟨⟨ω, fs.omega_mem⟩⟩
    let η : Env (rt_model_l C nc) 7 := ⟨Fin.cases ⟨g, hgC⟩ (Fin.cases ⟨e, heC⟩ (Fin.cases ⟨d, hdC⟩
      (Fin.cases ⟨F, lp.2⟩ (Fin.cases ⟨ρ, lp.1⟩ (Fin.cases ⟨κ, kp.1⟩ (fun _ => ⟨ω, fs.omega_mem⟩)))))), fun _ => ⟨ω, fs.omega_mem⟩⟩
    let η' : Env M 7 := ⟨Fin.cases g' (Fin.cases b' (Fin.cases d' (Fin.cases F' (Fin.cases ρ' (Fin.cases κ' (fun _ => ω)))))), fun _ => ω⟩
    have ultra := it_ultra_pull_l hZFC sb.transitive su.transitive mb mu hj fs nc hCV reflect η η' rfl
      (Fin.cases hgg (Fin.cases hee (Fin.cases hdd (Fin.cases hF (Fin.cases hρ (Fin.cases hκ (fun _ => omega))))))) parent mn family coherent ultra'
    obtain ⟨p₀,pay₀,active₀⟩ := ultra.active_l hZF (owner.read_source_l hZF) mx owner.theory
      parent mn loc agree family coherent
    have eqp : p₀ = p := by
      obtain ⟨r₀,p₀r,r₀f⟩ := pay₀
      have eqr := kpair_unique_l M hZF.1 r₀f tf
      exact kpair_unique_l M hZF.1 (eqr ▸ p₀r) pt
    exact ⟨k,a,d,e,g,p,pred,ha,hd,he,⟨r,pair,hg⟩,hp,Or.inr (eqp ▸ active₀)⟩
  · intro δ hδ limit
    obtain ⟨i, hi, succ⟩ := hw.exists_predecessor_of_mem_of_nonempty hZF hδ limit.2.1
    exact (it_successor_not_limit_l hZF.1 (hw.members_areOrdinals (ZF.modelsKP hZF) i hi) succ limit).elim
  · intro i ρ
    constructor
    · intro hl
      obtain ⟨ρ', hl', hρ⟩ := imageL hl
      obtain ⟨p', κ', F', hp', pay'⟩ := (big.levels i ρ').mp hl'
      obtain ⟨p, _, hp, hpp⟩ := read ef big.tree.move_function hEE (nat i (lf.2 i ρ hl).1) (lf.2 i ρ hl).1 hp'
      obtain ⟨κ, ρ₀, F, pay, _, hρ₀, _⟩ := it_payload_pull_l hZF hw sb.transitive su.transitive mb mu hj hpp pay'
      exact ⟨p, κ, F, hp, (hj.1.2 ρ₀ ρ ρ' hρ₀ hρ) ▸ pay⟩
    · rintro ⟨p, κ, F, hp, pay⟩
      obtain ⟨p', hp', hpp⟩ := image ef hEE hp
      obtain ⟨κ', ρ', F', pay', _, hρ, _⟩ := payload hpp pay
      obtain ⟨ρ₀, _, hl, hρ₀⟩ := hj.partial_entry_preimage_l hZF hw sb.transitive su.transitive vt mb mu hCV hL big.function hLL (nat i (ef.bound_l hp).1)
        ((big.levels i ρ').mpr ⟨p', κ', F', hp', pay'⟩)
      exact (hj.1.2 ρ₀ ρ ρ' hρ₀ hρ) ▸ hl
  · intro i p κ ρ F hp pay
    obtain ⟨p', hp', hpp⟩ := image ef hEE hp
    obtain ⟨κ', ρ', F', pay', hκ, hρ, hF⟩ := payload hpp pay
    obtain ⟨a',Y,W,ha',my,_,strength,inaccessible⟩ := big.exactness i p' κ' ρ' F' hp' pay'
    obtain ⟨a,_,ha,haa⟩ := read qf big.tree.diagram.model_function hQQ
      (nat i (ef.bound_l hp).1) (ef.bound_l hp).1 ha'
    obtain ⟨X₀, P₀, H, σ, mx₀, sx, hXY, res, hs, _⟩ := model ha' haa my
    exact ⟨a,X₀,P₀,ha,mx₀,sx.transitive,
      strength.pull_l hZF sb.transitive su.transitive mb mu hj su.theory sb.omega_mem sx hXY hκ hρ hF,
      inaccessible.pull_l hZF hw mx₀ my hs ((res.2 ω ω).mpr ⟨sx.omega_mem, omega⟩)
        ((res.2 ρ ρ').mpr ⟨(hj.member_l I hZF hw mb mu hρ hXY).mpr inaccessible.2.1, hρ⟩)⟩
  · intro i j ρ φ hi hj' hij
    obtain ⟨ρ', hi', hρ⟩ := imageL hi
    obtain ⟨φ', hj', hφ⟩ := imageL hj'
    exact (hj.member_l I hZF hw mb mu hρ hφ).mpr (big.increasing i j ρ' φ' hi' hj' hij)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 复制树结点给出像尝试树中的实际节点

模型及枚举使用同一外层嵌入的实际像。末端沿坐标逆图接回原复制嵌入，
有限行的值保留原自然数编号；联合尝试绝对性把这些实际节点放入像树。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_history_d.attempt_l {ω T Q G E L H Q' G' U o X₀ A₀ π₀ z₀ Z₀ α₀
    a₀ S₀ B R i X A π z Z α : M.Domain}
    (hist : Ic_history_d hZF ω T Q G E L ω H T Q' G')
    (tree : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G) (en : Ja_enum_d I ω ω Q U)
    (start : Ic_at_d H o X₀ A₀ π₀ z₀ Z₀ α₀) (ho : ∀ x, ¬ M.mem x o)
    (first : Smem_d I a₀ A₀ S₀) (space : Ja_space_d I ω T Q G U A₀ S₀ o π₀ B R)
    (hT : M.mem T Z₀) (hQ : M.mem Q Z₀) (hG : M.mem G Z₀) (hU : M.mem U Z₀)
    (hπ : M.mem π₀ Z₀) (hB : M.mem B Z₀) (hR : M.mem R Z₀) (here : Ic_at_d H i X A π z Z α) :
    ∃ g a S q B' R' P s Qᵢ Gᵢ Uᵢ, It_map_d G' o i g ∧ Smem_d I a A S ∧
      Rd_entry_d π₀ q g ∧ Rd_entry_d B B' g ∧ Rd_entry_d R R' g ∧
      Rd_entry_d Q Qᵢ g ∧ Rd_entry_d G Gᵢ g ∧ Rd_entry_d U Uᵢ g ∧
      It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Qᵢ Gᵢ ∧ Ja_enum_d I ω ω Qᵢ Uᵢ ∧
      Ja_space_d I ω T Qᵢ Gᵢ Uᵢ A S o q B' R' ∧ KPair_d M s i P ∧ M.mem s B' ∧
      Ja_node_d I ω T Qᵢ Gᵢ Uᵢ A S o q i P ∧
      ∀ k p, Rd_entry_d k p P → ∀ n y, Rd_entry_d n y p ↔ M.mem n i ∧ Ja_value_d G U i π k n y := by
  obtain ⟨c₀, hc₀, hz₀, row₀⟩ := hist.row_l hZF start
  obtain ⟨c, hc, hz, row⟩ := hist.row_l hZF here
  obtain ⟨V₀, W₀, R₀, b₀, _, _, mx₀, _, mz₀, _, full₀, hA₀, _, _, old⟩ := row₀
  obtain ⟨V, S, Rz, a, _, _, mx, ma, mz, _, full, hA, _, _, copied⟩ := row
  have hω := full₀.source.omega
  have hi := (tree.model_domain i).mpr ⟨c, hc⟩
  have hoω := (tree.model_domain o).mpr ⟨c₀, hc₀⟩
  have root := tree.order.root_l hZF ho i hi
  obtain ⟨g, hg⟩ := hist.diagram.map_l hZF root
  have j := hist.diagram.elementary o i g z₀ Z₀ R₀ z Z Rz hg hz₀ hz mz₀.1 mz.1
  obtain ⟨Qᵢ, Gᵢ, Uᵢ, tt, qq, gg, uu, diagram, enumeration, enums, maps, models⟩ :=
    it_countable_image_l hZF hω tree en full₀.source.transitive full.source.transitive mz₀ mz j
      (full₀.source.algebra_l (ZF.modelsKP hZF)) full₀.source.omega_mem hT hQ hG hU
  obtain ⟨cᵢ, Xᵢ, Vᵢ, v, hcᵢ, mxᵢ, _, back, inverse⟩ := models i c X V hc mx
  obtain ⟨τ, terminal, composition⟩ := it_comp_elementary_l hZF back copied
  obtain ⟨c₁, X₁, V₁, v₀, _, _, xx₀, back₀, inverse₀⟩ := models o c₀ X₀ V₀ hc₀ mx₀
  have aa := hist.cuts o i X₀ A₀ π₀ z₀ Z₀ α₀ X A π z Z α g start here hg
  have ss := ep_set_membership_l hZF full₀.source full.source mz₀ mz j first ma aa
  obtain ⟨q, _, pq⟩ := j.1.1.2.2 π₀ hπ
  obtain ⟨B', _, bb⟩ := j.1.1.2.2 B hB
  obtain ⟨R', _, rr⟩ := j.1.1.2.2 R hR
  have ww := j.omega_l I hZF hω full₀.source.transitive full.source.transitive mz₀ mz full₀.source.omega_mem
  have oo := j.natural_l hZF hω full₀.source.transitive full.source.transitive mz₀ mz full₀.source.omega_mem o hoω
  let ρ (Q G U A S q B R : M.Domain) : Env M 11 := ⟨Fin.cases ω (Fin.cases T (Fin.cases Q
    (Fin.cases G (Fin.cases U (Fin.cases A (Fin.cases S (Fin.cases o (Fin.cases q (Fin.cases B (fun _ => R)))))))))), fun _ => ω⟩
  have images : ∀ k, Rd_entry_d ((ρ Q G U A₀ S₀ π₀ B R).bound k) ((ρ Qᵢ Gᵢ Uᵢ A S q B' R').bound k) g :=
    Fin.cases ww (Fin.cases tt (Fin.cases qq (Fin.cases gg (Fin.cases uu
      (Fin.cases aa (Fin.cases ss (Fin.cases oo (Fin.cases pq (Fin.cases bb (fun _ => rr))))))))))
  have image := space.full_image_l hZF full₀.source full.source mz₀ mz j
    (ρ Q G U A₀ S₀ π₀ B R) (ρ Qᵢ Gᵢ Uᵢ A S q B' R') rfl images diagram enumeration
  have fn := (j.function_l hZF hω full₀.source.transitive full.source.transitive mz₀ mz xx₀ aa pq).mp
    (fn0_of_function_l (ZF.modelsKP hZF) old.1.1)
  obtain ⟨f, hf⟩ := tree.map_l hZF root
  have native := tree.elementary o i f c₀ X₀ V₀ c X V hf hc₀ hc mx₀ mx
  have fZ := hf.elim fun _ h => (rd_entry_transitive_l full₀.source.transitive hG h.2).2
  obtain ⟨f', _, ff⟩ := j.1.1.2.2 f fZ
  have hf' := (maps o i f').mpr ⟨f, hf, ff⟩
  have prescribed x' y (hxy : Rd_entry_d x' y q) :
      ∃ f v, It_map_d Gᵢ o i f ∧ Rd_entry_d x' v f ∧ Rd_entry_d v y τ := by
    obtain ⟨x, hx, hxx⟩ := back₀.1.1.2.2 x' (fn.bound_l hxy).1
    have xx := ((inverse₀ x' x).mp hxx).2
    obtain ⟨u, hu, hxu⟩ := old.1.1.2.2 x hx
    obtain ⟨v, hv, hxv⟩ := native.1.1.2.2 x hx
    obtain ⟨w, _, huw⟩ := j.1.1.2.2 u (full₀.source.transitive A₀ hA₀ u hu)
    have hxy' := (j.entry_l hZF hω full₀.source.transitive full.source.transitive mz₀ mz xx huw pq).mp hxu
    have eq := fn.2.2 x' (fn.bound_l hxy).1 w (fn.bound_l hxy').2 y (fn.bound_l hxy).2 hxy' hxy
    have result := eq ▸ hist.squares o i X₀ A₀ π₀ z₀ Z₀ α₀ X A π z Z α f g
      start here hf hg x u v w hxu hxv huw
    obtain ⟨v', _, vv⟩ := j.1.1.2.2 v (rd_entry_transitive_l full₀.source.transitive fZ hxv).2
    exact ⟨f', v', hf', (j.entry_l hZF hω full₀.source.transitive full.source.transitive mz₀ mz xx vv ff).mp hxv,
      (composition.2 v' y).mpr ⟨v, (inverse v' v).mpr ⟨hv, vv⟩, result⟩⟩
  obtain ⟨P, node, values⟩ := ja_node_of_l hZF hω diagram enumeration hi hcᵢ mxᵢ ma.1 terminal prescribed
  have same := ja_value_image_l hZF hω tree diagram en enumeration full₀.source.transitive full.source.transitive
    mz₀ mz j full₀.source.omega_mem hG hU enums maps hc mx hcᵢ mxᵢ
    (fn0_of_function_l (ZF.modelsKP hZF) copied.1.1) inverse composition
  obtain ⟨s, pair⟩ := (I).total i P
  exact ⟨g, a, S, q, B', R', P, s, Qᵢ, Gᵢ, Uᵢ, hg, ma, pq, bb, rr, qq, gg, uu, diagram, enumeration,
    image, pair, (image.nodes s).mpr ⟨i, P, pair, node⟩, node, fun k p hp n y =>
      (values k p hp n y).trans (and_congr_right fun hn => same k n y (hω.transitive (ZF.modelsKP hZF) i hi n hn))⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 联合尝试沿复制树边严格延伸

先从像中的有限行逐坐标回收到原行，再用实际复制方块把旧行值送到新行。
原树的复合律保证所有前驱行同时延伸；长度的严格增加给出真正的尝试树边。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_history_d.attempt_extend_l {ω T Q G E L H Q' G' U Q₀ G₀ U₀ Q₁ G₁ U₁ k l X A π z Z α Y B σ v V β
    S W o q q' D D' F P P' s t g : M.Domain}
    (hist : Ic_history_d hZF ω T Q G E L ω H T Q' G')
    (tree : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G)
    (image₀ : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q₀ G₀) (enum₀ : Ja_enum_d I ω ω Q₀ U₀)
    (image₁ : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q₁ G₁) (enum₁ : Ja_enum_d I ω ω Q₁ U₁)
    (left : Ic_at_d H k X A π z Z α) (right : Ic_at_d H l Y B σ v V β)
    (edge : It_map_d G' k l g) (lt : M.mem k l)
    (node : Ja_node_d I ω T Q₀ G₀ U₀ A S o q k P)
    (next : Ja_node_d I ω T Q₁ G₁ U₁ B W o q' l P')
    (values : ∀ i p, Rd_entry_d i p P → ∀ n y, Rd_entry_d n y p ↔ M.mem n k ∧ Ja_value_d G U k π i n y)
    (later : ∀ i p, Rd_entry_d i p P' → ∀ n y, Rd_entry_d n y p ↔ M.mem n l ∧ Ja_value_d G U l σ i n y)
    (pair : KPair_d M s k P) (pair' : KPair_d M t l P') (hs : M.mem s D)
    (dd : Rd_entry_d D D' g) (space : Ja_space_d I ω T Q₁ G₁ U₁ B W o q' D' F) :
    ∃ u, Rd_entry_d s u g ∧ Rd_entry_d t u F := by
  obtain ⟨c, hc, hz, row⟩ := hist.row_l hZF left
  obtain ⟨d, hd, hv, row'⟩ := hist.row_l hZF right
  obtain ⟨Rx, _, Rz, _, _, _, mx, _, mz, _, source, _, _, _, pi⟩ := row
  obtain ⟨Ry, _, Rv, _, _, _, my, _, mv, _, target, _, _, _, _⟩ := row'
  have hω := source.source.omega
  have j := hist.diagram.elementary k l g z Z Rz v V Rv edge hz hv mz.1 mv.1
  have hk := j.natural_l hZF hω source.source.transitive target.source.transitive mz mv source.source.omega_mem k node.length
  have hsZ := source.source.transitive D (j.1.1.input_mem_of_pairMember dd) s hs
  have hP := (pair.mem_l M source.source.transitive hsZ).2
  obtain ⟨u, hu, su⟩ := j.1.1.2.2 s hsZ
  obtain ⟨P₁, _, pp⟩ := j.1.1.2.2 P hP
  have pair₁ := (j.kpair_l hZF hω source.source.transitive target.source.transitive mz mv su hk pp).mp pair
  have huD := ((mv.2 u D').mp ((j.relation_l I hZF hω mz.1 mv.1 su dd).mp
    ((mz.2 s D).mpr ⟨hsZ, j.1.1.input_mem_of_pairMember dd, hs⟩))).2.2
  obtain ⟨k₁, P₂, pair₂, shifted⟩ := (space.nodes u).mp huD
  obtain ⟨ek, ep⟩ := kpair_injective_l M pair₂ pair₁
  subst k₁ P₂
  have kl := hist.diagram.map_bound_l hZF edge
  obtain ⟨f, hf⟩ := tree.map_l hZF kl
  have original := tree.elementary k l f c X Rx d Y Ry hf hc hd mx my
  have natural := j.natural_l hZF hω source.source.transitive target.source.transitive mz mv source.source.omega_mem
  have extend i p r (hip : Rd_entry_d i p P₁) (hir : Rd_entry_d i r P') : M.MemberSubset p r := by
    have ik := (shifted.domain i).mp ⟨p, hip⟩
    have hi := (tree.order.bound i k ik).1
    obtain ⟨a, C, R, ha, mc⟩ := image₀.model_l hZF hi
    obtain ⟨e, he⟩ := (enum₀.domain i).mp hi
    obtain ⟨b, D, S, hb, md⟩ := image₁.model_l hZF hi
    obtain ⟨e', he'⟩ := (enum₁.domain i).mp hi
    obtain ⟨p₀, hp₀⟩ := (node.domain i).mpr ik
    have fn₀ := (node.rows i p₀ a C R e hp₀ ha mc.1 he).1
    have fn := (shifted.rows i p b D S e' hip hb md.1 he').1
    obtain ⟨p₁, _, p01⟩ := j.1.1.2.2 p₀ (rd_entry_transitive_l source.source.transitive hP hp₀).2
    have entry := (j.entry_l hZF hω source.source.transitive target.source.transitive mz mv (natural i hi) p01 pp).mp hp₀
    have eq := shifted.function.2 i p₁ p entry hip
    subst p₁
    intro a₁ ha₁
    obtain ⟨n, hn, y, _, pairy⟩ := fn.1 a₁ ha₁
    have hny : Rd_entry_d n y p := ⟨a₁, pairy, ha₁⟩
    obtain ⟨x, _, hnx⟩ := fn₀.2.1 n hn
    obtain ⟨y₀, _, xy⟩ := j.1.1.2.2 x (rd_entry_transitive_l source.source.transitive
      (rd_entry_transitive_l source.source.transitive hP hp₀).2 hnx).2
    have hny₀ := (j.entry_l hZF hω source.source.transitive target.source.transitive mz mv
      (natural n (hω.transitive (ZF.modelsKP hZF) k node.length n hn)) xy p01).mp hnx
    have eq := (fn0_function_l (ZF.modelsKP hZF) fn).1.2 n y₀ y hny₀ hny
    subst y₀
    obtain ⟨_, e₀, f₀, b, w, he₀, hf₀, hnb, hbw, hwx⟩ := (values i p₀ hp₀ n x).mp hnx
    obtain ⟨w', _, hww⟩ := original.1.1.2.2 w (pi.1.1.input_mem_of_pairMember hwx)
    obtain ⟨f₁, hf₁⟩ := tree.map_l hZF (tree.order.trans i k l ik kl)
    have hwy := hist.squares k l X A π z Z α Y B σ v V β f g left right hf edge w x w' y hwx hww xy
    have hnr := (later i r hir n y).mpr ⟨(hω.members_areOrdinals (ZF.modelsKP hZF) l next.length).transitive k lt n hn,
      e₀, f₁, b, w', he₀, hf₁, hnb, tree.comp i k l f₀ f f₁ hf₀ hf hf₁ b w w' hbw hww, hwy⟩
    obtain ⟨a₂, pair₂, ha₂⟩ := hnr
    exact kpair_unique_l M hZF.1 pair₂ pairy ▸ ha₂
  exact ⟨u, su, (space.edges u t).mpr ⟨huD, (space.nodes t).mpr ⟨l, P', pair', next⟩,
    k, P₁, l, P', pair₁, pair', lt, kl, extend⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 移位秩值的原图定义

秩值是在复制根图的像中，对末结点嵌入唯一确定的联合节点求值。
所有见证均取自已构造的复制历史，定义不另加可延伸性或下降假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Jr_value_d (H G' T G U o F i δ : M.Domain) : Prop := ∃ X A π z Z α g F' P s,
  Ic_at_d H i X A π z Z α ∧ It_map_d G' o i g ∧ Rd_entry_d F F' g ∧
    Ja_lift_d I T G U i π P ∧ KPair_d M s i P ∧ Rd_entry_d s δ F'

def jr_value_m {d} (H G' T G U o F i δ : Term d) : Formula 1 d := set[d] ⟪
  ∃ X A π z Z α g F' P s, ⌜ic_at_m⌝ₚ(⌜H⌝ₛ, ⌜i⌝ₛ, X, A, π, z, Z, α) ∧
    ⌜it_map_m⌝ₚ(⌜G'⌝ₛ, ⌜o⌝ₛ, ⌜i⌝ₛ, g) ∧ ⌜rd_entry0_m⌝ₚ(⌜F⌝ₛ, F', g) ∧
    ⌜ja_lift_m⌝ₚ(⌜T⌝ₛ, ⌜G⌝ₛ, ⌜U⌝ₛ, ⌜i⌝ₛ, π, P) ∧
    ⌜kpair0_m⌝ₚ(s, ⌜i⌝ₛ, P) ∧ ⌜rd_entry0_m⌝ₚ(s, ⌜δ⌝ₛ, F')⟫
derive_free_closed jr_value_m

theorem jr_value_sat_l (hE : Extensional M) {d} (ρ : Env M d) (H G' T G U o F i δ : Term d) :
    Formula.satisfies ρ (jr_value_m H G' T G U o F i δ) ↔
      Jr_value_d I (H.eval ρ) (G'.eval ρ) (T.eval ρ) (G.eval ρ) (U.eval ρ) (o.eval ρ) (F.eval ρ) (i.eval ρ) (δ.eval ρ) := by
  simp only [jr_value_m, Jr_value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    ic_at_sat_l hE, it_map_sat_l hE, rd_entry0_sat_l hE, ja_lift_sat_l I hE,
    kpair0_sat_l hE, Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF)
local notation "J" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_history_d.embedding_l {ω T Q G E L H Q' G' i X A π z Z α k Y B σ v V β g : M.Domain}
    (hist : Ic_history_d hZF ω T Q G E L ω H T Q' G') (left : Ic_at_d H i X A π z Z α)
    (right : Ic_at_d H k Y B σ v V β) (edge : It_map_d G' i k g) :
    ∃ R S K K', Smem_d J z Z R ∧ Smem_d J v V S ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω K Z R ∧
      Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω K' V S ∧ Smap_d J ω z v Z V g := by
  obtain ⟨c, _, hz, row⟩ := hist.row_l hZF left
  obtain ⟨d, _, hv, row'⟩ := hist.row_l hZF right
  obtain ⟨_, _, R, _, _, K, _, _, mz, _, source, _⟩ := row
  obtain ⟨_, _, S, _, _, K', _, _, mv, _, target, _⟩ := row'
  exact ⟨R, S, K, K', mz, mv, source.source, target.source,
    hist.diagram.elementary i k g z Z R v V S edge hz hv mz.1 mv.1⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从实际复制树构造整列移位下降高度

每个高度是根秩图的像在唯一联合节点处的值。替代收集全部内部自然数
上的值；任意严格树边都由联合尝试延伸和同一秩图的不等式给出严格下降。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_history_d.rank_l {ω T Q G E L H Q' G' U o X₀ A₀ π₀ z₀ Z₀ α₀ a₀ S₀ B R η F : M.Domain}
    (hist : Ic_history_d hZF ω T Q G E L ω H T Q' G')
    (tree : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G) (en : Ja_enum_d I ω ω Q U)
    (start : Ic_at_d H o X₀ A₀ π₀ z₀ Z₀ α₀) (ho : ∀ x, ¬ M.mem x o)
    (first : Smem_d I a₀ A₀ S₀) (space : Ja_space_d I ω T Q G U A₀ S₀ o π₀ B R)
    (rank : Rr_d I B R η F) (hη : M.mem η Z₀) (hF : M.mem F Z₀)
    (hT : M.mem T Z₀) (hQ : M.mem Q Z₀) (hG : M.mem G Z₀) (hU : M.mem U Z₀)
    (hπ : M.mem π₀ Z₀) (hB : M.mem B Z₀) (hR : M.mem R Z₀) :
    ∃ D, M.IsSetFunction I D ∧ M.IsDomainOf I ω D ∧
      (∀ i δ, Rd_entry_d i δ D ↔ Jr_value_d I H G' T G U o F i δ) ∧
      (∀ i X A π z Z α δ, Ic_at_d H i X A π z Z α → Rd_entry_d i δ D →
        M.mem δ Z ∧ M.IsLimitOrdinal δ ∧ Sc_regular_d Z δ ∧
          ∃ g ε, It_map_d G' o i g ∧ Rd_entry_d η ε g ∧ M.mem ε δ) ∧
      ∀ k l g δ ε, It_map_d G' k l g → M.mem k l → Rd_entry_d k δ D → Rd_entry_d l ε D →
        ∃ γ, Rd_entry_d δ γ g ∧ M.mem ε γ := by
  have attempt {i X A π z Z α} (here : Ic_at_d H i X A π z Z α) :=
    hist.attempt_l hZF tree en start ho first space hT hQ hG hU hπ hB hR here
  have image {i X A π z Z α g F'} (here : Ic_at_d H i X A π z Z α)
      (hg : It_map_d G' o i g) (ff : Rd_entry_d F F' g) :
      ∃ B' R' η', Rd_entry_d B B' g ∧ Rd_entry_d R R' g ∧ Rd_entry_d η η' g ∧
        M.IsSetFunction I F' ∧ M.IsDomainOf I B' F' ∧
        (∀ s δ, Rd_entry_d s δ F' → M.IsLimitOrdinal δ ∧ Sc_regular_d Z δ ∧ M.mem η' δ) ∧
        ∀ s t δ ε, Rd_entry_d s t R' → Rd_entry_d s δ F' → Rd_entry_d t ε F' → M.mem δ ε := by
    obtain ⟨R₀, Rz, _, _, mz₀, mz, source, target, j⟩ := hist.embedding_l hZF start here hg
    obtain ⟨B', _, bb⟩ := j.1.1.2.2 B hB
    obtain ⟨R', _, rr⟩ := j.1.1.2.2 R hR
    obtain ⟨η', _, hh⟩ := j.1.1.2.2 η hη
    exact ⟨B', R', η', bb, rr, hh, rank.image_l hZF source.omega source.transitive target.transitive
      mz₀ mz j (source.algebra_l (ZF.modelsKP hZF)) bb rr hh ff⟩
  have total i (hi : M.mem i ω) : ∃ δ, Jr_value_d I H G' T G U o F i δ := by
    obtain ⟨_, X, A, π, z, Z, α, here, _⟩ := hist.at_l hZF hi
    obtain ⟨g, a, S, q, B', R', P, s, Qᵢ, Gᵢ, Uᵢ, hg, _, _, bb, _, _, _, _, di, ei, _, pair, hs, node, values⟩ := attempt here
    obtain ⟨_, _, _, _, _, _, _, _, j⟩ := hist.embedding_l hZF start here hg
    obtain ⟨F', _, ff⟩ := j.1.1.2.2 F hF
    obtain ⟨B₁, _, _, bb₁, _, _, _, dom, _⟩ := image here hg ff
    have eq := j.1.1.1.2 B B₁ B' bb₁ bb
    subst B₁
    obtain ⟨δ, value⟩ := (dom s).mp hs
    exact ⟨δ, X, A, π, z, Z, α, g, F', P, s, here, hg, ff, node.lift_l hZF di ei values, pair, value⟩
  have unique i δ ε (h : Jr_value_d I H G' T G U o F i δ) (k : Jr_value_d I H G' T G U o F i ε) : δ = ε := by
    obtain ⟨X, A, π, z, Z, α, g, F', P, s, here, hg, ff, lift, pair, value⟩ := h
    obtain ⟨X₁, A₁, π₁, z₁, Z₁, α₁, g₁, F₁, P₁, s₁, here₁, hg₁, ff₁, lift₁, pair₁, value₁⟩ := k
    obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := here₁.unique_l (ZF.modelsKP hZF) hist.function here
    subst X₁ A₁ π₁ z₁ Z₁ α₁
    have eg := hist.diagram.map_unique_l hZF hg₁ hg
    subst g₁
    obtain ⟨_, _, _, _, _, _, _, _, j⟩ := hist.embedding_l hZF start here hg
    have ef := j.1.1.1.2 F F₁ F' ff₁ ff
    subst F₁
    have ep := lift₁.unique_l (ZF.modelsKP hZF) lift
    subst P₁
    have es := kpair_unique_l M hZF.1 pair₁ pair
    subst s₁
    obtain ⟨_, _, _, _, _, _, fn, _⟩ := image here hg ff
    exact fn.2 s δ ε value value₁
  let ρ : Env M 7 := ⟨Fin.cases F (Fin.cases o (Fin.cases U (Fin.cases G
    (Fin.cases T (Fin.cases G' (fun _ => H)))))), fun _ => F⟩
  let φ : BinarySchema 7 := {
    body := jr_value_m (.bound 8) (.bound 7) (.bound 6) (.bound 5)
      (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have read i δ : φ.denote ρ i δ ↔ Jr_value_d I H G' T G U o F i δ := jr_value_sat_l I hZF.1 ..
  obtain ⟨V, vs⟩ := ZF.exists_functionalImage hZF φ ρ ω
    (fun i hi => (total i hi).imp fun δ hd => (read i δ).mpr hd)
    (fun i δ ε hd he => unique i δ ε ((read i δ).mp hd) ((read i ε).mp he))
  obtain ⟨D, df, ds⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (fun i hi => (total i hi).imp fun δ hd => (read i δ).mpr hd)
    (fun i _ δ ε hd he => unique i δ ε ((read i δ).mp hd) ((read i ε).mp he))
    (fun i δ hi hd => (vs δ).mpr ⟨i, hi, hd⟩)
  have spec i δ : Rd_entry_d i δ D ↔ Jr_value_d I H G' T G U o F i δ := (ds i δ).trans
    ⟨fun h => (read i δ).mp h.2, fun h => ⟨by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨r, hr, _⟩, _⟩ := h
      exact (hist.domain i).mpr ⟨r, hr⟩, (read i δ).mpr h⟩⟩
  refine ⟨D, df.1, df.2.1, spec, ?_, ?_⟩
  · intro i X A π z Z α δ here hd
    obtain ⟨X₁, A₁, π₁, z₁, Z₁, α₁, g, F', P, s, here₁, hg, ff, _, _, value⟩ := (spec i δ).mp hd
    obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := here₁.unique_l (ZF.modelsKP hZF) hist.function here
    subst X₁ A₁ π₁ z₁ Z₁ α₁
    obtain ⟨_, _, _, _, _, _, _, target, j⟩ := hist.embedding_l hZF start here hg
    obtain ⟨_, _, η', _, _, hh, _, _, regular, _⟩ := image here hg ff
    obtain ⟨limit, reg, above⟩ := regular s δ value
    exact ⟨(rd_entry_transitive_l target.transitive (j.1.1.output_mem_of_pairMember ff) value).2,
      limit, reg, g, η', hg, hh, above⟩
  · intro k l g δ ε edge lt hd he
    obtain ⟨X, A, π, z, Z, α, f, Fk, Pk, s, left, hf, ff, lift, pair, value⟩ := (spec k δ).mp hd
    obtain ⟨Y, B₁, σ, v, V, β, h, Fl, Pl, t, right, hh, fh, lift', pair', value'⟩ := (spec l ε).mp he
    obtain ⟨f₀, _, Sk, qk, Bk, Rk, P₀, s₀, Qk, Gk, Uk, hf₀, _, _, bk, _, _, _, _, dk, ek, _, ps₀, hs, node, values⟩ := attempt left
    have eq := hist.diagram.map_unique_l hZF hf₀ hf
    subst f₀
    have eq := (node.lift_l hZF dk ek values).unique_l (ZF.modelsKP hZF) lift
    subst P₀
    have eq := kpair_unique_l M hZF.1 ps₀ pair
    subst s₀
    obtain ⟨h₀, _, Sl, ql, Bl, Rl, P₁, t₀, Ql, Gl, Ul, hh₀, _, _, bl, rl, _, _, _, dl, el, space', pt₀, _, next, later⟩ := attempt right
    have eq := hist.diagram.map_unique_l hZF hh₀ hh
    subst h₀
    have eq := (next.lift_l hZF dl el later).unique_l (ZF.modelsKP hZF) lift'
    subst P₁
    have eq := kpair_unique_l M hZF.1 pt₀ pair'
    subst t₀
    obtain ⟨_, Rz, _, _, _, mz, _, source, jf⟩ := hist.embedding_l hZF start left hf
    obtain ⟨_, Rv, _, _, _, mv, _, target, jh⟩ := hist.embedding_l hZF start right hh
    obtain ⟨_, _, hz, _⟩ := hist.row_l hZF left
    obtain ⟨_, _, hv, _⟩ := hist.row_l hZF right
    have j := hist.diagram.elementary k l g z Z Rz v V Rv edge hz hv mz.1 mv.1
    have cross x a b (ha : Rd_entry_d x a f) (hb : Rd_entry_d x b h) : Rd_entry_d a b g := by
      obtain ⟨b', _, hab⟩ := j.1.1.2.2 a (jf.1.1.output_mem_of_pairMember ha)
      exact jh.1.1.1.2 x b' b (hist.diagram.comp o k l f g h hf edge hh x a b' ha hab) hb ▸ hab
    obtain ⟨u, su, tu⟩ := hist.attempt_extend_l hZF tree dk ek dl el left right edge lt node next values later pair pair' hs (cross B Bk Bl bk bl) space'
    have hδ := (rd_entry_transitive_l source.transitive (jf.1.1.output_mem_of_pairMember ff) value).2
    obtain ⟨γ, _, dg⟩ := j.1.1.2.2 δ hδ
    have ug := (j.entry_l hZF source.omega source.transitive target.transitive mz mv su dg (cross F Fk Fl ff fh)).mp value
    obtain ⟨_, R₁, _, _, rr, _, _, _, _, decrease⟩ := image right hh fh
    have eq := jh.1.1.1.2 R R₁ Rl rr rl
    subst R₁
    exact ⟨γ, dg, decrease t u ε γ tu value' ug⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 移位高度给出完整 nice 树的实际秩段

每个移位高度严格超过原目标秩段高度的像，故新秩段包含所属扩展器和
支撑。相对层级唯一性使结构码列可由替代收集；根高度保留背景正则性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

private def Jr_cut_d (ω H D i a : M.Domain) : Prop := ∃ X A π z Z α δ V S,
  Ic_at_d H i X A π z Z α ∧ Rd_entry_d i δ D ∧ Smem_d I a V S ∧
    M.mem V Z ∧ Vr_d Z δ V ∧ M.mem ω V ∧ M.MemberSubset A V

private def jr_cut_m {d} (ω H D i a : Term d) : Formula 1 d := set[d] ⟪
  ∃ X A π z Z α δ V S, ⌜ic_at_m⌝ₚ(⌜H⌝ₛ, ⌜i⌝ₛ, X, A, π, z, Z, α) ∧
    ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, δ, ⌜D⌝ₛ) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜a⌝ₛ, V, S) ∧
    V ∈ Z ∧ ⌜pn_rank_m⌝ₚ(Z, δ, V) ∧ ⌜ω⌝ₛ ∈ V ∧ A ⊆ V⟫
derive_free_closed jr_cut_m

private theorem jr_cut_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω H D i a : Term d) :
    Formula.satisfies ρ (jr_cut_m ω H D i a) ↔
      Jr_cut_d I (ω.eval ρ) (H.eval ρ) (D.eval ρ) (i.eval ρ) (a.eval ρ) := by
  simp only [jr_cut_m, Jr_cut_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    ic_at_sat_l hKP.1, rd_entry0_sat_l hKP.1, smem_sat_l I, Formula.satisfies_mem_iff,
    pn_rank_sat_l hKP, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF)
local notation "J" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_history_d.rank_cut_l {ω c T Q G E L H Q' G' U o X₀ A₀ π₀ z₀ Z₀ α₀ a₀ S₀ B R F : M.Domain}
    (hist : Ic_history_d hZF ω T Q G E L ω H T Q' G')
    (tree : It_tree_d hZF ω c ω T Q G E)
    (levels : ∀ i ρ, Rd_entry_d i ρ L ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F)
    (lf : M.IsSetFunction J L) (en : Ja_enum_d J ω ω Q U)
    (start : Ic_at_d H o X₀ A₀ π₀ z₀ Z₀ α₀) (ho : ∀ x, ¬ M.mem x o)
    (first : Smem_d J a₀ A₀ S₀) (space : Ja_space_d J ω T Q G U A₀ S₀ o π₀ B R)
    (rank : Rr_d J B R α₀ F) (hα : M.mem α₀ Z₀) (hF : M.mem F Z₀)
    (hT : M.mem T Z₀) (hQ : M.mem Q Z₀) (hG : M.mem G Z₀) (hU : M.mem U Z₀)
    (hπ : M.mem π₀ Z₀) (hB : M.mem B Z₀) (hR : M.mem R Z₀) :
    ∃ E' L' D N, It_pnice_d hZF ω z₀ ω T Q' G' E' L' ∧ It_cut_d hZF ω ω Q' E' D N ∧
      (∀ δ, Rd_entry_d o δ D → M.IsRegularCardinal J δ ∧ M.mem α₀ δ) ∧
      (∀ i p, Rd_entry_d i p E' → (∀ x, ¬ M.mem x p) → Rd_entry_d i p E) ∧
      ∀ k l g δ ε, It_map_d G' k l g → M.mem k l → Rd_entry_d k δ D → Rd_entry_d l ε D →
        ∃ γ, Rd_entry_d δ γ g ∧ M.mem ε γ := by
  obtain ⟨D, df, dom, values, heights, drop⟩ := hist.rank_l hZF tree.diagram en start ho first space rank
    hα hF hT hQ hG hU hπ hB hR
  obtain ⟨E', L', copied, moves⟩ := hist.nice_l hZF tree levels ho start
  obtain ⟨_, _, _, row₀⟩ := hist.row_l hZF start
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rank₀, _, _⟩ := row₀
  have contains {i X A π z Z α δ V} (here : Ic_at_d H i X A π z Z α) (hd : Rd_entry_d i δ D)
      (hV : M.mem V Z) (rv : Vr_d Z δ V) : M.MemberSubset A V := by
    obtain ⟨_, limit, _, g, ε, hg, he, below⟩ := heights i X A π z Z α δ here hd
    obtain ⟨_, _, _, _, mz₀, mz, source, target, j⟩ := hist.embedding_l hZF start here hg
    have aa := hist.cuts o i X₀ A₀ π₀ z₀ Z₀ α₀ X A π z Z α g start here hg
    have ra := (j.hierarchy_l hZF source.omega source.transitive target.transitive mz₀ mz he aa).mp rank₀
    exact (rv.compare_l hZF target.transitive hV (j.1.1.output_mem_of_pairMember aa) ra
      (limit.1.transitive ε below)).1
  have total i (hi : M.mem i ω) : ∃ a, Jr_cut_d J ω H D i a := by
    obtain ⟨_, X, A, π, z, Z, α, here, _, _, row⟩ := hist.at_l hZF hi
    obtain ⟨δ, hd⟩ := (dom i).mp hi
    obtain ⟨_, _, _, _, _, _, _, _, _, small, full, _⟩ := row
    obtain ⟨hδ, limit, _⟩ := heights i X A π z Z α δ here hd
    obtain ⟨V, hV, rv⟩ := (full.read_l hZF).1 δ hδ limit.1
    have sub := contains here hd hV rv
    have hw := sub ω small.omega_mem
    obtain ⟨a, S, ma⟩ := smdl_membership_l J hZF ⟨ω, hw⟩
    exact ⟨a, X, A, π, z, Z, α, δ, V, S, here, hd, ma, hV, rv, hw, sub⟩
  have unique i a b (ha : Jr_cut_d J ω H D i a) (hb : Jr_cut_d J ω H D i b) : a = b := by
    obtain ⟨X, A, π, z, Z, α, δ, V, S, here, hd, ma, hV, rv, _⟩ := ha
    obtain ⟨X₁, A₁, π₁, z₁, Z₁, α₁, δ₁, V₁, S₁, here₁, hd₁, mb, hV₁, rv₁, _⟩ := hb
    obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := here₁.unique_l (ZF.modelsKP hZF) hist.function here
    subst X₁ A₁ π₁ z₁ Z₁ α₁
    have eq := df.2 i δ₁ δ hd₁ hd
    subst δ₁
    obtain ⟨_, _, _, row⟩ := hist.row_l hZF here
    obtain ⟨_, _, _, _, _, _, _, _, _, _, full, _⟩ := row
    have eq := rv₁.unique_l hZF full.source.transitive hV₁ hV rv
    subst V₁
    exact (smem_unique_l J hZF.1 ma mb).1
  let ρ : Env M 3 := ⟨Fin.cases D (Fin.cases H (fun _ => ω)), fun _ => ω⟩
  let φ : BinarySchema 3 := { body := jr_cut_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have read i a : φ.denote ρ i a ↔ Jr_cut_d J ω H D i a := jr_cut_sat_l J (ZF.modelsKP hZF) ..
  obtain ⟨V, vs⟩ := ZF.exists_functionalImage hZF φ ρ ω
    (fun i hi => (total i hi).imp fun a ha => (read i a).mpr ha)
    (fun i a b ha hb => unique i a b ((read i a).mp ha) ((read i b).mp hb))
  obtain ⟨N, nf, ns⟩ := ZF.exists_setFunctionFromTo_of_denote hZF J φ ρ
    (fun i hi => (total i hi).imp fun a ha => (read i a).mpr ha)
    (fun i _ a b ha hb => unique i a b ((read i a).mp ha) ((read i b).mp hb))
    (fun i a hi ha => (vs a).mpr ⟨i, hi, ha⟩)
  have cut i a (ha : Rd_entry_d i a N) := (read i a).mp ((ns i a).mp ha).2
  refine ⟨E', L', D, N, copied, ⟨df, dom, nf.1, nf.2.1, ?_, ?_, ?_, ?_⟩, ?_, ?_, drop⟩
  · intro i z hz
    obtain ⟨_,X,A,π,z₁,Z,α,_,_,hz₁,row⟩ :=
      hist.at_l hZF ((hist.diagram.model_domain i).mpr ⟨z,hz⟩)
    have eq := hist.diagram.model_function.2 i z₁ z hz₁ hz
    subst z₁
    obtain ⟨_,_,R,_,_,_,_,_,model,_,full,_⟩ := row
    exact ⟨Z,R,model,full.source.transitive⟩
  · intro i z a δ Z R hz ha hd mz
    obtain ⟨X, A, π, z₁, Z₁, α, δ₁, V, S, here, hd₁, ma, hV, rv, hw, _⟩ := cut i a ha
    obtain ⟨_, _, hz₁, row⟩ := hist.row_l hZF here
    have eq := hist.diagram.model_function.2 i z₁ z hz₁ hz
    subst z₁
    obtain ⟨_, _, _, _, _, _, _, _, mz₁, _⟩ := row
    obtain ⟨ez, _⟩ := smdl_unique_l J mz₁.1 mz.1
    subst Z₁
    have eq := df.2 i δ₁ δ hd₁ hd
    subst δ₁
    exact ⟨V, S, ma, hV, rv, (heights i X A π z Z α δ here hd).2.2.1, hw⟩
  · intro i p κ ρ F a V S hp pay ha ma
    obtain ⟨X, A, π, z, Z, α, p₀, κ₀, ρ₀, F₀, κ₁, ρ₁, F₁, here, _, _, _, hρ, hF, pay₁⟩ := ((moves i p).mp hp).active_l pay
    obtain ⟨e₁, e₂, e₃⟩ := pay₁.unique_l pay
    subst κ₁ ρ₁ F₁
    obtain ⟨X₁, A₁, π₁, z₁, Z₁, α₁, _, V₁, _, here₁, _, ma₁, _, _, _, sub⟩ := cut i a ha
    obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := here₁.unique_l (ZF.modelsKP hZF) hist.function here
    subst X₁ A₁ π₁ z₁ Z₁ α₁
    obtain ⟨eq, _⟩ := smdl_unique_l J ma₁.1 ma.1
    subst V₁
    obtain ⟨_, _, _, row⟩ := hist.row_l hZF here
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, pi⟩ := row
    exact ⟨sub ρ (pi.1.1.output_mem_of_pairMember hρ), sub F (pi.1.1.output_mem_of_pairMember hF)⟩
  · intro i j p κ ρ F a V S succ hp pay ha ma
    obtain ⟨X, A, π, z, Z, α, p₀, κ₀, ρ₀, F₀, κ₁, ρ₁, F₁, ai, hp₀, pay₀, _, hρ, _, pay₁⟩ := ((moves i p).mp hp).active_l pay
    have eq := (pay₁.unique_l pay).2.1
    subst ρ₁
    obtain ⟨Y, B, σ, u, U, β, _, V₁, _, aj, _, ma₁, _, _, _, sub⟩ := cut j a ha
    obtain ⟨eq, _⟩ := smdl_unique_l J ma₁.1 ma.1
    subst V₁
    obtain ⟨l, φ, U₀, V₀, D₀, t₀, c, d, R₀, S₀, _, _, _, _, same⟩ :=
      (hist.past i j X A π z Z α Y B σ u U β ai aj succ.predecessor_mem).active_l
        (fun s t hs ht => lf.2 i s t hs ht) ((levels i ρ₀).mpr ⟨p₀, κ₀, F₀, hp₀, pay₀⟩)
    obtain ⟨_, _, _, row⟩ := hist.row_l hZF ai
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, ep⟩ := row
    have eq := ep.1.1.1.2 ρ₀ φ ρ same.left_end hρ
    subst φ
    obtain ⟨_, _, _, row'⟩ := hist.row_l hZF aj
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, es⟩ := row'
    exact sub ρ (es.1.1.output_mem_of_pairMember same.right_end)
  · intro δ hd
    obtain ⟨_, _, _, _, _, _, g, F', _, s, _, hg, ff, _, _, value⟩ := (values o δ).mp hd
    have eq := hist.diagram.identity o g hg F F' ff
    exact rank.regular s δ (eq.symm ▸ value)
  · intro i p hp empty
    rcases (moves i p).mp hp with ⟨hp, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, r, ⟨u, v, _, _, pair⟩, _⟩
    · exact hp
    · exact (empty u ((pair u).mpr (Or.inl rfl))).elim

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 返回失败自动产生正规根上的下降 nice 复制树

公共可数载体、联合尝试秩、容纳全部参数的正规根、完整复制历史及下降
秩段列均在本定理中构造。入口使用原可数树、其实际复制性质及到给定秩层的初等嵌入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_copyable_failure_l {ω c X R T Q G E o θ A a S π : M.Domain}
    (tree : It_tree_d hZF ω c ω T Q G E) (copyable : It_copyable_d hZF ω c T Q G E)
    (mx : Smem_d I c X R) (xt : M.TransitiveSet X)
    (count : M.CardinalLessOrEqual I X ω) (ho : ∀ x, ¬ M.mem x o)
    (rank : V_d I θ A) (ma : Smem_d I a A S)
    (embed : Smap_d I ω c a X A π) (bad : ¬ It_return_d hZF ω o T Q G a A π) :
    ∃ δ Z z Rz Q' G' E' L' D N, M.IsRegularCardinal I δ ∧ M.mem ω δ ∧ V_d I δ Z ∧ Smem_d I z Z Rz ∧
      It_pnice_d hZF ω z ω T Q' G' E' L' ∧
      (∀ i a Y S, Rd_entry_d i a Q' → Smem_d I a Y S → Sc_power_d Y) ∧ It_cut_d hZF ω ω Q' E' D N ∧
      (∀ β, Rd_entry_d o β D → M.IsRegularCardinal I β ∧ M.mem θ β) ∧
      (∀ i p, Rd_entry_d i p E' → (∀ x, ¬ M.mem x p) → Rd_entry_d i p E) ∧
      ∀ k l g β γ, It_map_d G' k l g → M.mem k l → Rd_entry_d k β D → Rd_entry_d l γ D →
        ∃ ε, Rd_entry_d β ε g ∧ M.mem γ ε := by
  obtain ⟨L,function,levels,copy⟩ := copyable
  have hω := tree.omega
  obtain ⟨X₀, R₀, K, mx₀, source⟩ := (tree.sources o c (tree.root o ho)).mem_l hZF ⟨X, R, mx, xt⟩
  obtain ⟨ex, er⟩ := smdl_unique_l I mx₀.1 mx.1
  subst X₀ R₀
  -- 初等像的配对闭包迫使原目标高度为极限，无需另作假设。
  have ht := v_transitive_l I rank
  have hωA := embed.1.1.output_mem_of_pairMember (embed.omega_l I hZF hω source.transitive ht mx ma source.omega_mem)
  have hθ := v_ordinal_l I rank
  have algebra := (source.theory.map_l I hZF hω mx.1 ma.1 embed).algebra_l I (ZF.modelsKP hZF) ht ma
  have limit : M.IsLimitOrdinal θ := by
    refine ⟨hθ, ⟨ω, ZF.v_ordinal_height_l hZF rank (hω.isOrdinal (ZF.modelsKP hZF)) hωA⟩, ?_⟩
    intro β hβ
    have hβA := ZF.v_ordinal_mem_l I hZF rank hβ
    obtain ⟨p, hp, pair⟩ := algebra.pair β β hβA hβA
    obtain ⟨γ, W, hγ, vw, sub⟩ := (ZF.v_unfold_l I hZF rank p).mp hp
    exact ⟨γ, hγ, ZF.v_ordinal_height_l hZF vw (hθ.mem hβ) (sub β ((pair β).mpr (Or.inl rfl)))⟩
  obtain ⟨U, B, W, F, en, space, regular⟩ := ja_failure_l hZFC tree mx.1 count ho ma
    (fn0_of_function_l (ZF.modelsKP hZF) embed.1.1) limit.1 bad
  let v : Fin 10 → M.Domain := Fin.cases T (Fin.cases Q (Fin.cases G
    (Fin.cases U (Fin.cases π (Fin.cases A (Fin.cases θ (Fin.cases B (Fin.cases W (fun _ => F)))))))))
  obtain ⟨P, _, ps⟩ := ZF.finite_params_l I hZF hω v
  obtain ⟨δ, Z, hδ, above, outer, hP⟩ := ZFC.v_regular_cover_l I hZFC hω P
  have owned i : M.mem (v i) Z := v_transitive_l I outer P hP (v i) ((ps (v i)).mpr ⟨i, rfl⟩)
  have hθ : M.mem θ δ := ZF.v_ordinal_height_l hZF outer limit.1 (owned 6)
  obtain ⟨B₀, F₀, hB₀, hF₀, cert, _⟩ := vr_source_l hZF outer hδ.isLimitOrdinal hθ rank
  have relative : Vr_d Z θ A := ⟨B₀, F₀, hB₀, hF₀, fun t _ => cert t⟩
  obtain ⟨z, row⟩ := ic_initial_row_l hZFC (it_source_mem_l hZF mx source) mx.1 ma embed above hδ outer (owned 5) relative limit
  obtain ⟨H,Q',G',hist,start⟩ := copy o X A π z Z θ ho row
  obtain ⟨E', L', D, N, copied, cut, root, pads, drop⟩ := hist.rank_cut_l hZF tree levels function en start ho ma space regular
    (owned 6) (owned 9) (owned 0) (owned 1) (owned 2) (owned 3) (owned 4) (owned 7) (owned 8)
  obtain ⟨_, _, Rz, _, _, _, _, _, mz, _⟩ := row
  refine ⟨δ, Z, z, Rz, Q', G', E', L', D, N, hδ, above, outer, mz, copied, ?_, cut, root, pads, drop⟩
  intro i a Y S ha my
  obtain ⟨_, _, _, _, a₀, Y₀, _, _, _, ha₀, row⟩ := hist.at_l hZF ((hist.diagram.model_domain i).mpr ⟨a, ha⟩)
  have eq := hist.diagram.model_function.2 i a₀ a ha₀ ha
  subst a₀
  obtain ⟨_, _, _, _, _, _, _, _, model, _, full, _⟩ := row
  obtain ⟨rfl, _⟩ := smdl_unique_l I model.1 my.1
  exact (full.read_l hZF).2.1

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 可复制的可数原关系树返回原秩层

实际复制性质来自 nice 树构造或 demanding 全运行。返回失败给出正则根上的真实下降复制树。
包含整棵树和截断列的可数反射壳
恢复同一含恒等步的 nice 树、同一秩段及下降值；原正则根给出初始行，双重基础反证排除失败。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 给定可数根到真实秩层的初等图，可复制原关系树有共尾良基枝及同一根图的返回因子。 -/
theorem it_copyable_return_l {ω c X R T Q G E o θ A a S π : M.Domain}
    (tree : It_tree_d hZF ω c ω T Q G E) (copyable : It_copyable_d hZF ω c T Q G E)
    (mx : Smem_d I c X R) (xt : M.TransitiveSet X)
    (count : M.CardinalLessOrEqual I X ω) (ho : ∀ x, ¬ M.mem x o)
    (rank : V_d I θ A) (ma : Smem_d I a A S) (embed : Smap_d I ω c a X A π) :
    It_return_d hZF ω o T Q G a A π := by
  classical
  have hw := tree.omega
  apply Classical.byContradiction
  intro bad
  -- 失败产生原树序上的真实下降复制树；整套列图同时进入反射壳。
  obtain ⟨δ, Z, z, Rz, Q', G', E', L', A', D', regular, above, outer, mz, copied, powers, cuts, root, _, drop⟩ :=
    it_copyable_failure_l hZFC tree copyable mx xt count ho rank ma embed bad
  have actual i a (ha : Rd_entry_d i a Q') := (copied.tree.sources i a ha).mem_l hZF (cuts.models i a ha)
  let v : Fin 5 → M.Domain := Fin.cases z (Fin.cases E' (Fin.cases L' (Fin.cases A' (fun _ => D'))))
  obtain ⟨B, Rb, b, K, U, Su, u, J, C, V, σ, q, g, sb, su, mb, mu, hs, countB, hC, fs, vt, hCV,
    hT, hq, hg, hTT, hQQ, hGG, diagram, _, reflect, params⟩ :=
    it_diagram_hull_l hZFC hw copied.tree.diagram copied.tree.sources v
  obtain ⟨c₀, _, hcc⟩ := params 0
  obtain ⟨e, he, hEE⟩ := params 1
  obtain ⟨l, hl, hLL⟩ := params 2
  obtain ⟨d, hd, hAA⟩ := params 3
  obtain ⟨n, hn, hDD⟩ := params 4
  have small := it_pnice_pull_l hZFC sb su mb mu hs hC fs vt hCV hq hg he hl
    hcc hTT hQQ hGG hEE hLL diagram copied cuts.models powers reflect
  have smallcuts := it_cut_pull_l hZF sb su mb mu hs hC fs.transitive vt hCV hq he hd hn
    hQQ hEE hAA hDD copied.tree.diagram actual cuts
  have hoω := (diagram.model_domain o).mpr ⟨c₀, small.tree.root o ho⟩
  -- 大根截断等于背景正则 Vβ；同一反塌缩的限制给出真实初始行。
  obtain ⟨a₀, ha₀⟩ := (smallcuts.code_domain o).mp hoω
  obtain ⟨a', _, haa⟩ := hs.1.1.2.2 a₀ (sb.transitive C hC a₀ (rd_entry_transitive_l fs.transitive hn ha₀).2)
  have ha' := (hs.entry_l hZF hw sb.transitive su.transitive mb mu
    (hs.natural_l hZF hw sb.transitive su.transitive mb mu sb.omega_mem o hoω) haa hDD).mp ha₀
  obtain ⟨β, hβ⟩ := (cuts.height_domain o).mp hoω
  obtain ⟨V₀, P₀, mv₀, hV₀, vr, reg, hωV⟩ := cuts.ranks o z a' β Z Rz (copied.tree.root o ho) ha' hβ mz
  obtain ⟨Z₀, R₀, _, mz₀, sz⟩ := actual o z (copied.tree.root o ho)
  obtain ⟨ez, er⟩ := smdl_unique_l I mz₀.1 mz.1
  subst Z₀ R₀
  have βreg := (root β hβ).1
  have βδ := ZF.v_ordinal_height_l hZF outer βreg.1.1 (sz.rank_height_l hZF hV₀ vr reg hωV).1
  obtain ⟨W, vw⟩ := ZF.v_exists_l I hZF βreg.1.1
  obtain ⟨P, F, hP, hF, vc, _⟩ := vr_source_l hZF outer regular.isLimitOrdinal βδ vw
  have eq := vr.unique_l hZF sz.transitive hV₀ (ZF.v_mem_l I hZF vw outer βδ) ⟨P, F, hP, hF, fun t _ => vc t⟩
  have actual : V_d I β V₀ := eq ▸ vw
  have ωβ := vr.ordinal_height_l hZF sz.transitive hV₀ (hw.isOrdinal (ZF.modelsKP hZF)) hωV
  obtain ⟨X₁, P₁, p, ι, _, _, _, initial⟩ := pn_initial_pull_l hZFC sb su mb mu hs countB haa mv₀ ωβ βreg actual
  -- 原下降值沿同一张图回拉，直接与已完成的模型／原高度双重基础反证矛盾。
  apply it_pnice_no_drop_l hZFC small smallcuts ho ha₀ initial
  intro i j k f α β _ pred edge hα hβ
  exact it_drop_pull_l hZF hw sb.transitive su.transitive mb mu hs sb.omega_mem hGG hAA drop
    k j f α β edge pred.1 ((smallcuts.height_domain k).mpr ⟨α, hα⟩) ((smallcuts.height_domain j).mpr ⟨β, hβ⟩) hα hβ

end YesMetaZFC.SetTheory.LargeCardinal
