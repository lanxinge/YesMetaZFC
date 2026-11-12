import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawEvaluation
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawConstant
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCopySyntax
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationApplication

/-! # 原对象码极限中的函数应用等式

每个实际支撑的坐标代表先进入同一原商，再沿原分量初等图进入极限。
全局常值图由共同支撑定理识别，因而所得等式使用原给定的常值像。
坐标代表和函数应用只调用当前原关系源自身的外延性、分离与收集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_graph_d.application_l {ω c' Y S Γ H k N T z L J O Z A p V W r c₂ C W' j α : M.Domain}
    (hω : M.IsOmega ω) (model : Smdl_d I c' Y S) (ext : Rf_ext_d I Y S)
    (theory : Sc_theory_d I ω Y S) (collection : Sc_collection_d I ω Y S)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := T) nx).Models KP)
    (U w ξ ℓ e : (smdl_structure_l I (R := T) nx).Domain)
    (numbers : Rr_layer_d I ω N T w.val z) (finite : Fs_read_d w U)
    (powers : ∀ m d : (smdl_structure_l I (R := T) nx).Domain,
      (smdl_structure_l I (R := T) nx).mem m w → Ep_space_d ξ m d →
        ∃ p, (smdl_structure_l I (R := T) nx).IsPowerSetOf p d)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (ownerClosed : Rr_closed_d I N T U.val) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (closed : Rr_closed_d I Y S H) (small : Rr_small_d I Y S H)
    (hξ : (smdl_structure_l I (R := T) nx).mem ξ U)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (h : Er_graph_d I ω L N T ξ.val ℓ.val e.val z Y S k J O Z A p V W)
    (diagram : Di_system_d J O A p V W) (limit : Di_limit_d A p V W r C W')
    (target : Smdl_d I c₂ C W') (constants : Er_constants_d Y r j)
    (hα : M.mem α J) (loc : It_local_d I w.val N T ξ.val ℓ.val e.val) :
    ∃ n, ∃ m β d : (smdl_structure_l I (R := T) nx).Domain, ∃ D t y a,
      M.mem n ω ∧ Rd_entry_d n m.val z ∧ Rr_finite_d I ω L N T z α β.val ∧
      Fn0_d m ℓ β ∧ Ep_space_d ξ m d ∧
      (∀ s, M.mem s D ↔ M.mem s N ∧ Rd_entry_d s d.val T) ∧
      Fn0_d D Y t ∧ M.IsRestrictionOf I t k D ∧ Rd_entry_d d.val y k ∧ Ep_repr_d r α t a ∧
      (∀ f g E F, Rf_fun_d I Y S y f → Rc_graph_d I Y S t f g →
        Ep_repr_d r α g E → Rd_entry_d f F j → Rf_val_d I C W' a E F) ∧
      (∀ x B E, KPair_d M x α B → Rd_entry_d x E r →
        ∃ f g, Rf_fun_d I Y S y f ∧ Rc_graph_d I Y S t f g ∧ Ep_repr_d r α g E) ∧
      Er_seed_d I ω L N T ξ.val e.val z Y S k r α a ∧
      (∀ b f u : (smdl_structure_l I (R := T) nx).Domain, ∀ b' f' E F,
        Fn0_d d b f → KPair_d (smdl_structure_l I (R := T) nx) u β f →
        Rd_entry_d b.val b' k → Rd_entry_d f.val f' k →
        Er_eval_d I ω L N T z Γ Y k r u.val E → Rd_entry_d f' F j → Rf_val_d I C W' a E F) := by
  obtain ⟨_, table⟩ := h.codes
  obtain ⟨o, _, hαo⟩ := table.2.1 α hα
  obtain ⟨q, identity, _⟩ := smap_identity_l I hZF (X := Y) (c := c') hω
  obtain ⟨n, m, β, d, v₀, hn, fα, hnm, fβ, gβ, fb, space, hd, hβv,
    D, i, t, y, P, U₀, G, s, C₀, W₀, dc, fi, id, rt, ft, hdy, _, source, ultra, measure, family, quotient⟩ :=
    (h.components α o hαo).read_l hZF hω model theory model identity nx hN U w ξ ℓ e numbers finite powers
      carrier ownerClosed fk image pred closed hξ length loc
  have hy := fk.1.output_mem_of_pairMember hdy
  let d' : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨y, hy⟩
  have domain v x (hvx : Rd_entry_d v x t) : Rd_entry_d x y S := (pred d.val y hdy x).mpr
    ⟨v, ((dc v).mp ((rt.2 v x).mp hvx).1).2, ((rt.2 v x).mp hvx).2⟩
  have en := ext.native_l I model.2.1
  have uniform := collection.uniform_l I (small y hy ((image y).mpr ⟨d.val, (carrier d.val).mpr ⟨d.property, hd⟩, hdy⟩))
  obtain ⟨v, hv, stage⟩ := h.stage_l hZF hω diagram limit target hαo quotient.code
  have ht := rc_coordinate_l hZF hω model ext theory d' ft domain family
  obtain ⟨B, hB, htB⟩ := quotient.map.projection.2.2 t ht
  obtain ⟨a, _, hBa⟩ := hv.1.1.2.2 B hB
  have repr {f B E} (hf : Rd_entry_d f B s) (hBE : Rd_entry_d B E v) : Ep_repr_d r α f E := by
    obtain ⟨_, u, pair, huE⟩ := (stage B E).mp hBE
    exact ⟨u, B, pair, quotient.map.representative_l I ultra.base hf, huE⟩
  have read {g E} (value : Ep_repr_d r α g E) : ∃ B, Rd_entry_d g B s ∧ Rd_entry_d B E v := by
    obtain ⟨u, B, pair, hgB, huE⟩ := value
    have hB := (ep_at_read_l table hαo quotient.code.1).mp (h.at_l (limit.projection.bound_l huE).1 pair)
    exact ⟨B, quotient.map.member_l I hZF.1 ultra.base hB hgB, (stage B E).mpr ⟨hB, u, pair, huE⟩⟩
  obtain ⟨l, hl, const⟩ := rc_constant_embedding_l hZF hω model ext theory
    d' uniform ft domain source ultra
    ((rc_family_native_l I model.2.1 en d' ft).mp family) quotient
  have frame : Er_frame_d I ω L N T ξ.val e.val z Y S k α o
      n m.val β.val d.val v₀.val D i t y U₀ G s C₀ W₀ :=
    ⟨hn, fα, hnm, fβ, gβ, (er_space_native_l I nx hN.1 ξ m d).mpr space,
      (rf_val_native_l I nx hN.1 β v₀ e).mpr hβv, dc, fn0_of_function_l (ZF.modelsKP hZF) fi,
      id, rt, hdy, measure, family, quotient⟩
  have seed : Er_seed_d I ω L N T ξ.val e.val z Y S k r α a := by
    obtain ⟨_, u, pair, hua⟩ := (stage B a).mp hBa
    exact ⟨o, n, m.val, β.val, d.val, v₀.val, D, i, t, y, U₀, G, s, C₀, W₀, B, u, frame, htB, pair, hua⟩
  have apply f g E F (ff : Rf_fun_d I Y S y f) (graph : Rc_graph_d I Y S t f g)
      (value : Ep_repr_d r α g E) (imageF : Rd_entry_d f F j) : Rf_val_d I C W' a E F := by
    obtain ⟨B', hgB, hBE⟩ := read value
    obtain ⟨K, hK, hfK⟩ := hl.1.1.2.2 f (ff.mem_l I)
    obtain ⟨_, k', hk, constant, hkK⟩ := (const f K).mp hfK
    obtain ⟨F', _, hKF⟩ := hv.1.1.2.2 K hK
    obtain ⟨α₀, D₀, k₀, fk₀, const₀, value₀⟩ := constants f F imageF
    have eq := h.constant_l hZF nx (kp_pair_l hN) hN.1 w ξ ℓ e numbers length loc diagram limit
      (quotient.map.functions k' hk) fk₀ constant const₀ (repr hkK hKF) value₀
    exact rc_application_l hZF hω model ext theory d' uniform ft domain source ultra family quotient target hv
      ff graph constant htB hgB hkK hBa hBE (eq ▸ hKF)
  refine ⟨n, m, β, d, D, t, y, a, hn, hnm, ⟨n, m.val, hn, fα, hnm, fβ, gβ⟩,
    fb, space, dc, ft, rt, hdy, repr htB hBa, apply, ?_, seed, ?_⟩
  · intro x B E pair hxE
    have hB := (ep_at_read_l table hαo quotient.code.1).mp (h.at_l (limit.projection.bound_l hxE).1 pair)
    obtain ⟨g, gp⟩ := (quotient.map.range B).mp hB
    obtain ⟨_, f, ff, graph⟩ := (family g).mp (quotient.map.projection.input_mem_of_pairMember gp)
    exact ⟨f, g, ff, graph, x, B, pair, quotient.map.representative_l I ultra.base gp, hxE⟩
  · intro b f u b' f' E F ff pair hbb hff value imageF
    obtain ⟨fn, g, decode, rep⟩ := value.function_l hZF numbers hN.1 model.2.1 en U u β f d b
      finite.transitive carrier fk pred ⟨n, m.val, hn, fα, hnm, fβ, gβ⟩ ff pair dc ft rt hdy hbb hff
    exact apply f' g E F fn decode rep imageF

end YesMetaZFC.SetTheory.LargeCardinal
