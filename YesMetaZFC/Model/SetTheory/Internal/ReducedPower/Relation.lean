import YesMetaZFC.SetTheory.Filter.Relative
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition

/-! # 内部约化幂的几乎处处关系

代表元都是模型内函数图。等同和关系由一个实际滤子成员上的逐点见证定义；
有限交共同细化直接给出等价性和关系对代表元替换的不变性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rp_eq_d (Q U f g : M.Domain) : Prop := ∃ A, M.mem A U ∧ ∀ i, M.mem i A →
  ∃ x, M.mem x Q ∧ Rd_entry_d i x f ∧ Rd_entry_d i x g

def rp_eq_m {d} (Q U f g : Term d) : Formula 1 d := Formula.existsMem U (Formula.forallMem .newest
  (Formula.existsMem Q.weaken.weaken (.conj (rd_entry0_m (.bound 1) .newest f.weaken.weaken.weaken)
    (rd_entry0_m (.bound 1) .newest g.weaken.weaken.weaken))))
derive_free_closed rp_eq_m

theorem rp_eq_delta_l {d} (Q U f g : Term d) : (rp_eq_m Q U f g).IsDelta0 :=
  .existsMem _ (.forallMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))

theorem rp_eq_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Q U f g : Term d) :
    Formula.satisfies ρ (rp_eq_m Q U f g) ↔ Rp_eq_d (Q.eval ρ) (U.eval ρ) (f.eval ρ) (g.eval ρ) := by
  simp only [rp_eq_m, Rp_eq_d, Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_conj_iff, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem rp_eq_refl_l {D Q U f} (hU : FilterZF.Base_d (ℳ := M) D U) (hf : Fn0_d D Q f) : Rp_eq_d Q U f f :=
  ⟨D, hU.top, fun i hi => (hf.2.1 i hi).imp fun _ hx => ⟨hx.1, hx.2, hx.2⟩⟩

theorem rp_eq_member_l {D Q P U f g A} (hU : FilterZF.Rel_ultra_d (ℳ := M) D P U)
    (hA : M.mem A P) (hs : ∀ v, M.mem v A ↔ M.mem v D ∧
      ∃ x, M.mem x Q ∧ Rd_entry_d v x f ∧ Rd_entry_d v x g) : M.mem A U ↔ Rp_eq_d Q U f g := by
  refine ⟨fun h => ⟨A, h, fun v hv => ((hs v).mp hv).2⟩, ?_⟩
  rintro ⟨B, hB, hb⟩
  exact hU.upward B A hB hA (fun v hv => (hs v).mpr ⟨hU.base.bounds B hB v hv, hb v hv⟩)

theorem Rp_eq_d.symm_l {Q U f g : M.Domain} (h : Rp_eq_d Q U f g) : Rp_eq_d Q U g f :=
  h.imp fun _ ha => ⟨ha.1, fun i hi => (ha.2 i hi).imp fun _ hx => ⟨hx.1, hx.2.symm⟩⟩

theorem Rp_eq_d.trans_l {D Q U f g h} (hU : FilterZF.Base_d (ℳ := M) D U) (hg : Fn0_d D Q g)
    (hfg : Rp_eq_d Q U f g) (hgh : Rp_eq_d Q U g h) : Rp_eq_d Q U f h := by
  obtain ⟨A, hAU, hA⟩ := hfg
  obtain ⟨B, hBU, hB⟩ := hgh
  obtain ⟨C, hCU, hCA, hCB⟩ := hU.meet A B hAU hBU
  refine ⟨C, hCU, fun i hi => ?_⟩
  obtain ⟨x, hx, hxf, hxg⟩ := hA i (hCA i hi)
  obtain ⟨y, hy, hyg, hyh⟩ := hB i (hCB i hi)
  have eq := hg.2.2 i (hg.bound_l hxg).1 y hy x hx hyg hxg
  exact ⟨x, hx, hxf, eq ▸ hyh⟩

def Rp_rel_d (Q U R f g : M.Domain) : Prop := ∃ A, M.mem A U ∧ ∀ i, M.mem i A →
  ∃ x, M.mem x Q ∧ ∃ y, M.mem y Q ∧ Rd_entry_d i x f ∧ Rd_entry_d i y g ∧ M.PairMember I x y R

def rp_rel_m {d} (Q U R f g : Term d) : Formula 1 d := Formula.existsMem U (Formula.forallMem .newest
  (Formula.existsMem Q.weaken.weaken (Formula.existsMem Q.weaken.weaken.weaken (.conj
    (rd_entry0_m (.bound 2) (.bound 1) f.weaken.weaken.weaken.weaken) (.conj
      (rd_entry0_m (.bound 2) .newest g.weaken.weaken.weaken.weaken)
      (Formula.orderedPairMem 𝒞 (.bound 1) .newest R.weaken.weaken.weaken.weaken))))))
derive_free_closed rp_rel_m

theorem rp_rel_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Q U R f g : Term d) :
    Formula.satisfies ρ (rp_rel_m (𝒞 := 𝒞) Q U R f g) ↔
      Rp_rel_d I (Q.eval ρ) (U.eval ρ) (R.eval ρ) (f.eval ρ) (g.eval ρ) := by
  simp only [rp_rel_m, Rp_rel_d, Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_conj_iff, rd_entry0_sat_l hE, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  rfl

theorem rp_rel_transport_l {D Q U R f g f' g'} (hU : FilterZF.Base_d (ℳ := M) D U)
    (hf : Fn0_d D Q f) (hg : Fn0_d D Q g) (he : Rp_eq_d Q U f f') (hk : Rp_eq_d Q U g g')
    (h : Rp_rel_d I Q U R f g) : Rp_rel_d I Q U R f' g' := by
  obtain ⟨A, hAU, hA⟩ := he
  obtain ⟨B, hBU, hB⟩ := h
  obtain ⟨C, hCU, hC⟩ := hk
  obtain ⟨E, hEU, hEA, hEB⟩ := hU.meet A B hAU hBU
  obtain ⟨T, hTU, hTE, hTC⟩ := hU.meet E C hEU hCU
  refine ⟨T, hTU, fun i hi => ?_⟩
  obtain ⟨x, hx, hxf, hxf'⟩ := hA i (hEA i (hTE i hi))
  obtain ⟨y, hy, z, hz, hyf, hzg, hyz⟩ := hB i (hEB i (hTE i hi))
  obtain ⟨w, hw, hwg, hwg'⟩ := hC i (hTC i hi)
  have ey := hf.2.2 i (hf.bound_l hxf).1 y hy x hx hyf hxf
  have ez := hg.2.2 i (hg.bound_l hwg).1 z hz w hw hzg hwg
  exact ⟨x, hx, w, hw, hxf', hwg', ey ▸ ez ▸ hyz⟩

theorem rp_rel_congr_l {D Q U R f g f' g'} (hU : FilterZF.Base_d (ℳ := M) D U)
    (hf : Fn0_d D Q f) (hg : Fn0_d D Q g) (hf' : Fn0_d D Q f') (hg' : Fn0_d D Q g')
    (he : Rp_eq_d Q U f f') (hk : Rp_eq_d Q U g g') : Rp_rel_d I Q U R f g ↔ Rp_rel_d I Q U R f' g' :=
  ⟨rp_rel_transport_l I hU hf hg he hk, rp_rel_transport_l I hU hf' hg' he.symm_l hk.symm_l⟩

end YesMetaZFC.SetTheory.Internal
