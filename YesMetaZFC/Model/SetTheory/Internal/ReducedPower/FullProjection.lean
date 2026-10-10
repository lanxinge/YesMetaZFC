import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Lift
import YesMetaZFC.SetTheory.Filter.Projection

/-! # 完整测度在任意源代表族上的原子投影

代表族可以仅包含源内部函数。背景分离形成精确原子真值集，测度投影直接
给出等价及关系的保持、反映；不把整个背景函数空间替换进源超幂。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rp_atom_d (b : Bool) (X R f g v : M.Domain) : Prop := ∃ x, M.mem x X ∧ ∃ y, M.mem y X ∧
  Rd_entry_d v x f ∧ Rd_entry_d v y g ∧ (if b then x = y else M.PairMember I x y R)

def rp_atom_m (b : Bool) {d} (X R f g v : Term d) : Formula 1 d := Formula.existsMem X
  (Formula.existsMem X.weaken (.conj (rd_entry_m v.weaken.weaken (.bound 1) f.weaken.weaken)
    (.conj (rd_entry_m v.weaken.weaken .newest g.weaken.weaken)
      (if b then Formula.extensionalEq (.bound 1) .newest else Formula.orderedPairMem 𝒞 (.bound 1) .newest R.weaken.weaken))))
@[simp] theorem rp_atom_closed_l (b : Bool) {d} (X R f g v : Term d)
    (hX : X.freeSupport = []) (hR : R.freeSupport = []) (hf : f.freeSupport = [])
    (hg : g.freeSupport = []) (hv : v.freeSupport = []) : (rp_atom_m (𝒞 := 𝒞) b X R f g v).FreeClosed := by
  cases b <;> simp -implicitDefEqProofs [rp_atom_m, Definitional.Formula.FreeClosed, hX, hR, hf, hg, hv]

theorem rp_atom_sat_l (hE : Extensional M) (b : Bool) {d} (ρ : Env M d) (X R f g v : Term d) :
    Formula.satisfies ρ (rp_atom_m (𝒞 := 𝒞) b X R f g v) ↔
      Rp_atom_d I b (X.eval ρ) (R.eval ρ) (f.eval ρ) (g.eval ρ) (v.eval ρ) := by
  cases b <;> simp only [rp_atom_m, Rp_atom_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    rd_entry_sat_l hE, Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_orderedPairMem_iff I,
    Bool.false_eq_true, ↓reduceIte, Definitional.Term.eval_weaken] <;> rfl

theorem rp_atom_eq_l {X U R f g : M.Domain} :
    (∃ A, M.mem A U ∧ ∀ v, M.mem v A → Rp_atom_d I true X R f g v) ↔ Rp_eq_d X U f g := by
  refine exists_congr fun A => and_congr_right fun _ => forall_congr' fun v => imp_congr_right fun _ => ?_
  exact ⟨fun ⟨x, hx, y, _, hfx, hgy, e⟩ => ⟨x, hx, hfx, e.symm ▸ hgy⟩,
    fun ⟨x, hx, hfx, hgx⟩ => ⟨x, hx, x, hx, hfx, hgx, rfl⟩⟩

theorem rp_pull_atom_l (hZF : M.Models ZF) (b : Bool) {D E X R P Q U V t f g f' g' : M.Domain}
    (hP : M.IsPowerSetOf P D) (hU : Rel_ultra_d D P U) (hV : Rel_ultra_d E Q V)
    (ht : Push_d D E P Q U V t) (hf : Fn0_d D X f) (hg : Fn0_d D X g)
    (hF : Cp0_d E D X t f f') (hG : Cp0_d E D X t g g') :
    (∃ A, M.mem A U ∧ ∀ v, M.mem v A → Rp_atom_d I b X R f g v) ↔
      ∃ B, M.mem B V ∧ ∀ v, M.mem v B → Rp_atom_d I b X R f' g' v := by
  let ρ := (((⟨fun _ => X, fun _ => X⟩ : Env M 1).push R).push f).push g
  let φ : UnarySchema 4 := { body := rp_atom_m (𝒞 := 𝒞) b (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨A, ha⟩ := ZF.separation_exists_d hZF φ ρ D
  have hA v : M.mem v A ↔ M.mem v D ∧ Rp_atom_d I b X R f g v :=
    (ha v).trans (and_congr_right fun _ => rp_atom_sat_l I hZF.1 b _ _ _ _ _ _)
  obtain ⟨B, hBQ, hb, he⟩ := ht.2 A ((hP A).mpr fun v hv => ((hA v).mp hv).1)
  have hB v : M.mem v B ↔ M.mem v E ∧ Rp_atom_d I b X R f' g' v := by
    refine (hb v).trans ⟨?_, ?_⟩
    · rintro ⟨hv, w, hw, hvw⟩
      obtain ⟨_, x, hx, y, hy, hfx, hgy, hxy⟩ := (hA w).mp hw
      exact ⟨hv, x, hx, y, hy, (hF.value_l ht.1 hf hvw).mpr hfx, (hG.value_l ht.1 hg hvw).mpr hgy, hxy⟩
    · rintro ⟨hv, x, hx, y, hy, hfx, hgy, hxy⟩
      obtain ⟨w, hw, hvw⟩ := ht.1.2.1 v hv
      exact ⟨hv, w, (hA w).mpr ⟨hw, x, hx, y, hy, (hF.value_l ht.1 hf hvw).mp hfx,
        (hG.value_l ht.1 hg hvw).mp hgy, hxy⟩, hvw⟩
  have old : M.mem A U ↔ ∃ C, M.mem C U ∧ ∀ v, M.mem v C → Rp_atom_d I b X R f g v :=
    ⟨fun h => ⟨A, h, fun v hv => ((hA v).mp hv).2⟩, fun ⟨C, hC, hh⟩ => hU.upward C A hC
      ((hP A).mpr fun v hv => ((hA v).mp hv).1) (fun v hv => (hA v).mpr ⟨hU.base.bounds C hC v hv, hh v hv⟩)⟩
  have new : M.mem B V ↔ ∃ C, M.mem C V ∧ ∀ v, M.mem v C → Rp_atom_d I b X R f' g' v :=
    ⟨fun h => ⟨B, h, fun v hv => ((hB v).mp hv).2⟩, fun ⟨C, hC, hh⟩ => hV.upward C B hC hBQ
      (fun v hv => (hB v).mpr ⟨hV.base.bounds C hC v hv, hh v hv⟩)⟩
  exact old.symm.trans (he.symm.trans new)

theorem rp_full_projection_l (hZF : M.Models ZF) {D E X R P Q U V t F G c d p q C N S T K : M.Domain}
    (hP : M.IsPowerSetOf P D) (hU : Rel_ultra_d D P U) (hV : Rel_ultra_d E Q V)
    (ht : Push_d D E P Q U V t) (hp : Rp_model_d I D X U R c F p C S) (hq : Rp_model_d I E X V R d G q N T)
    (hK : M.IsSetFunctionFromTo I K F G) (hk : ∀ f g, M.PairMember I f g K → Cp0_d E D X t f g) :
    ∃ j, M.IsSetInjectionFromTo I j C N ∧ Rp_lift_d I K p q j ∧
      ∀ B D B' D', M.PairMember I B B' j → M.PairMember I D D' j →
        (M.PairMember I B D S ↔ M.PairMember I B' D' T) := by
  obtain ⟨j, hj, lift⟩ := rp_lift_exists_l I hZF hU.base hV.base hp.map hq.map hK (fun f g f' g' hf hg =>
    (rp_atom_eq_l I (R := R)).symm.trans ((rp_pull_atom_l I hZF true hP hU hV ht
      (hp.map.functions f (hK.input_mem_of_pairMember hf)) (hp.map.functions g (hK.input_mem_of_pairMember hg))
      (hk f f' hf) (hk g g' hg)).trans (rp_atom_eq_l I)))
  refine ⟨j, hj, lift, fun B D B' D' hBB' hDD' => ?_⟩
  obtain ⟨f, hfp⟩ := (hp.map.range B).mp (hj.1.input_mem_of_pairMember hBB')
  obtain ⟨g, hgp⟩ := (hp.map.range D).mp (hj.1.input_mem_of_pairMember hDD')
  obtain ⟨f', hf', hff'⟩ := hK.2.2 f (hp.map.projection.input_mem_of_pairMember hfp)
  obtain ⟨g', hg', hgg'⟩ := hK.2.2 g (hp.map.projection.input_mem_of_pairMember hgp)
  obtain ⟨B'', _, hfq⟩ := hq.map.projection.2.2 f' hf'
  obtain ⟨D'', _, hgq⟩ := hq.map.projection.2.2 g' hg'
  have eb := hj.1.1.2 B B'' B' (lift f f' B B'' hff' hfp hfq) hBB'
  have ed := hj.1.1.2 D D'' D' (lift g g' D D'' hgg' hgp hgq) hDD'
  subst B'' D''
  exact (hp.relation f g B D hfp hgp).trans ((rp_pull_atom_l I hZF false hP hU hV ht
    (hp.map.functions f (hp.map.projection.input_mem_of_pairMember hfp))
    (hp.map.functions g (hp.map.projection.input_mem_of_pairMember hgp)) (hk f f' hff') (hk g g' hgg')).trans
      (hq.relation f' g' B' D' hfq hgq).symm)

end YesMetaZFC.SetTheory.Internal
