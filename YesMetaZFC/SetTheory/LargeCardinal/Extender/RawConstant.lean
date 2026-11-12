import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawGraphSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower
import YesMetaZFC.Model.SetTheory.ReducedPower.SourceModel

/-! # 对象码极限中同支撑的原子方程

类的原代表、商关系和极限投影依次读取。把代表移到共同支撑时保留
同一个极限值，随后原子方程仍使用该分量的实际测度。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω L N T ξ ℓ e z Y S k J O Z A p V W r C W' : M.Domain}

theorem Er_graph_d.repr_atoms_l (h : Er_graph_d I ω L N T ξ ℓ e z Y S k J O Z A p V W)
    (diagram : Di_system_d J O A p V W) (limit : Di_limit_d A p V W r C W')
    {a o D U G s C₀ W₀ f g E H : M.Domain} (hao : Rd_entry_d a o Z)
    (quotient : Rp_model_d I D Y U S o G s C₀ W₀) (base : Base_d D U)
    (fv : Ep_repr_d r a f E) (gv : Ep_repr_d r a g H) :
    (E = H ↔ Rp_eq_d Y U f g) ∧ (Rd_entry_d E H W' ↔ Rp_rel_d I Y U S f g) := by
  obtain ⟨u, B, pu, hf, huE⟩ := fv
  obtain ⟨v, D, pv, hg, hvH⟩ := gv
  have huA := (limit.projection.bound_l huE).1
  have hvA := (limit.projection.bound_l hvH).1
  have hua := (h.index u a B pu).mpr huA
  have hva := (h.index v a D pv).mpr hvA
  obtain ⟨_, table⟩ := h.codes
  have hBC := (ep_at_read_l table hao quotient.code.1).mp (h.at_l huA pu)
  have hDC := (ep_at_read_l table hao quotient.code.1).mp (h.at_l hvA pv)
  have fp := quotient.map.member_l I hZF.1 base hBC hf
  have gp := quotient.map.member_l I hZF.1 base hDC hg
  have same : u = v ↔ B = D := ⟨fun eq => (kpair_injective_l M (eq ▸ pu) pv).2,
    fun eq => kpair_unique_l M hZF.1 (eq ▸ pu) pv⟩
  refine ⟨(limit.kernel u v E H huE hvH).trans
    ((diagram.eq_at_l hua hva).trans (same.trans (rp_kernel_l I hZF.1 base quotient.map fp gp))), ?_⟩
  exact (limit.relation u v E H huE hvH).trans
    ((diagram.rel_at_l hua hva (diagram.identity u huA) (diagram.identity v hvA)).trans
      ((h.relation_l pu pv).trans ((and_congr_right fun _ => and_congr_right fun _ =>
        ep_rel_read_l table hao quotient.code.1).trans
          ((and_iff_right huA).trans ((and_iff_right hvA).trans (quotient.relation f g B D fp gp))))))

theorem Er_graph_d.reindex_l (h : Er_graph_d I ω L N T ξ ℓ e z Y S k J O Z A p V W)
    (diagram : Di_system_d J O A p V W) (limit : Di_limit_d A p V W r C W')
    {a b q f E : M.Domain} (hb : M.mem b J) (edge : Ei_map_d ω L a b q) (value : Ep_repr_d r a f E) :
    ∃ D Q t g, Er_coord_d I ω L N T ξ ℓ z a b D Q t ∧ Cp0_d Q D Y t f g ∧ Ep_repr_d r b g E := by
  obtain ⟨u, B, pu, hf, huE⟩ := value
  have hua := (h.index u a B pu).mpr (limit.projection.bound_l huE).1
  have ab := (h.order_spec a b).mpr ⟨(h.projection.bound_l hua).2, hb, q, edge⟩
  obtain ⟨v, hvb, huv⟩ := diagram.total u a b hua ab
  obtain ⟨C, pv, _⟩ := h.label_l hvb
  obtain ⟨D, Q, t, g, coord, hg, pull⟩ := h.lift_l hZF.1 pu pv huv hf
  obtain ⟨E', _, hvE⟩ := limit.projection.2.1 v (h.projection.bound_l hvb).1
  exact ⟨D, Q, t, g, coord, pull, v, C, pv, hg, (limit.commute_l diagram huv huE hvE).symm ▸ hvE⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 任意支撑的常值代表在原关系极限中一致

把两份原代表移到实际共同支撑，复合图仍处处取同一个值。该分量的原
测度迹提供滤子基，商的等号核与极限交换律遂识别两份值。所属结构只需
配对解释与外延性；这里不在其中重建超滤或调用分离、替换公理。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 超幂边的逐点常值证书；同一极限中的所有值都有实际代表。 -/
def Er_constants_d (Y r j : M.Domain) : Prop := ∀ x E, Rd_entry_d x E j →
  ∃ a D f, Fn0_d D Y f ∧ Rs_const_d D x f ∧ Ep_repr_d r a f E

def er_constants_m {n} (Y r j : Term n) : Formula 1 n := set[n] ⟪∀ x E,
  ⌜rd_entry0_m⌝ₚ(x, E, ⌜j⌝ₛ) → ∃ a D f,
    ⌜fn0_m⌝ₚ(D, ⌜Y⌝ₛ, f) ∧ ⌜rs_const_m⌝ₚ(D, x, f) ∧ ⌜ep_repr_m⌝ₚ(⌜r⌝ₛ, a, f, E)⟫
derive_free_closed er_constants_m

theorem er_constants_sat_l (ext : Extensional M) {n} (ρ : Env M n) (Y r j : Term n) :
    Formula.satisfies ρ (er_constants_m Y r j) ↔ Er_constants_d (Y.eval ρ) (r.eval ρ) (j.eval ρ) := by
  simp only [er_constants_m, Er_constants_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l ext,
    fn0_sat_l ext, rs_const_sat_l ext, ep_repr_sat_l ext, Definitional.Term.eval_weaken]
  rfl

theorem Er_graph_d.constant_l {ω L N T z Y S k J O Z A p V W r C W' D E x a b f g H P : M.Domain}
    (nx : ∃ x, M.mem x N) (K : kpair_convention_l.Interpretation (smdl_structure_l I (R := T) nx))
    (ext : Extensional (smdl_structure_l I (R := T) nx))
    (w ξ ℓ e : (smdl_structure_l I (R := T) nx).Domain)
    (numbers : Rr_layer_d I ω N T w.val z)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (loc : It_local_d I w.val N T ξ.val ℓ.val e.val)
    (h : Er_graph_d I ω L N T ξ.val ℓ.val e.val z Y S k J O Z A p V W)
    (diagram : Di_system_d J O A p V W) (limit : Di_limit_d A p V W r C W')
    (ff : Fn0_d D Y f) (fg : Fn0_d E Y g) (fc : Rs_const_d D x f) (gc : Rs_const_d E x g)
    (fv : Ep_repr_d r a f H) (gv : Ep_repr_d r b g P) : H = P := by
  obtain ⟨u, B, pu, hf, huH⟩ := fv
  obtain ⟨v, B', pv, hg, hvP⟩ := gv
  obtain ⟨α, s, t, hsα, htα, hus, hvt⟩ :=
    diagram.common_l (limit.projection.bound_l huH).1 (limit.projection.bound_l hvP).1
  obtain ⟨Q, ps, o, C₀, W₀, hαo, pair, hQC⟩ := h.label_l hsα
  obtain ⟨Q', pt, atQ'⟩ := h.label_l htα
  obtain ⟨_, table⟩ := h.codes
  have hQ'C := (ep_at_read_l table hαo pair).mp atQ'
  obtain ⟨D₀, U₀, G₀, q₀, C₁, W₁, quotient, base⟩ :=
    (h.components α o hαo).base_l hZF nx K ext w ξ ℓ e numbers length loc
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair quotient.code.1
  have lift {D a B u f Q s} (ff : Fn0_d D Y f) (fc : Rs_const_d D x f)
      (pu : KPair_d M u a B) (hf : M.mem f B) (ps : KPair_d M s α Q)
      (hQC : M.mem Q C₀) (hus : Rd_entry_d u s V) :
      ∃ g, M.mem g Q ∧ Rs_const_d D₀ x g := by
    obtain ⟨D₁, D₂, t, g, _, hg, pull⟩ := h.lift_l hZF.1 pu ps hus hf
    have gp := quotient.map.member_l I hZF.1 base hQC hg
    have fn := quotient.map.functions g (quotient.map.projection.input_mem_of_pairMember gp)
    have eq := pull.1.domain_eq_l hZF.1 fn
    subst D₂
    refine ⟨g, hg, fun s hs => ?_⟩
    obtain ⟨v, _, y, _, _, hvy, hsy⟩ := pull.2 s hs
    have value := fc v (ff.bound_l hvy).1
    exact ((fn0_function_l (ZF.modelsKP hZF) ff).1.2 v y x hvy value) ▸ hsy
  obtain ⟨f', hf', fc'⟩ := lift ff fc pu hf ps hQC hus
  obtain ⟨g', hg', gc'⟩ := lift fg gc pv hg pt hQ'C hvt
  have fp := quotient.map.member_l I hZF.1 base hQC hf'
  have gp := quotient.map.member_l I hZF.1 base hQ'C hg'
  have fn := quotient.map.functions f' (quotient.map.projection.input_mem_of_pairMember fp)
  have eq := (rp_kernel_l I hZF.1 base quotient.map fp gp).mpr
    ⟨D₀, base.top, fun s hs => ⟨x, (fn.bound_l (fc' s hs)).2, fc' s hs, gc' s hs⟩⟩
  have same := kpair_unique_l M hZF.1 ps (eq.symm ▸ pt)
  exact (limit.kernel u v H P huH hvP).mpr ⟨s, hus, same.symm ▸ hvt⟩

/-- 同一实际原极限上的全定义常值图唯一，因而可直接使用已给定的活动边。 -/
theorem Er_graph_d.constants_unique_l {ω L N T z Y S k J O Z A p V W r C W' j j' : M.Domain}
    (nx : ∃ x, M.mem x N) (K : kpair_convention_l.Interpretation (smdl_structure_l I (R := T) nx))
    (ext : Extensional (smdl_structure_l I (R := T) nx))
    (w ξ ℓ e : (smdl_structure_l I (R := T) nx).Domain)
    (numbers : Rr_layer_d I ω N T w.val z)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (loc : It_local_d I w.val N T ξ.val ℓ.val e.val)
    (h : Er_graph_d I ω L N T ξ.val ℓ.val e.val z Y S k J O Z A p V W)
    (diagram : Di_system_d J O A p V W) (limit : Di_limit_d A p V W r C W')
    (fj : Fn0_d Y C j) (fj' : Fn0_d Y C j') (cj : Er_constants_d Y r j) (cj' : Er_constants_d Y r j') : j = j' := by
  apply fj.ext_l hZF.1 fj'
  intro x hx
  obtain ⟨B, _, hxB⟩ := fj.2.1 x hx
  obtain ⟨E, _, hxE⟩ := fj'.2.1 x hx
  obtain ⟨a, D, f, ff, fc, fv⟩ := cj x B hxB
  obtain ⟨b, D', g, fg, gc, gv⟩ := cj' x E hxE
  have eq := h.constant_l hZF nx K ext w ξ ℓ e numbers length loc diagram limit ff fg fc gc fv gv
  exact ⟨B, hxB, eq.symm ▸ hxE⟩

end YesMetaZFC.SetTheory.LargeCardinal
