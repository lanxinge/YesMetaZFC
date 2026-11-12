import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawPresent
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawExactHistory

/-! # 原最大强度证书与支撑以下的双向子集读取

直接展开原证书中的幂集像、节点池和求值图。原秩源包含支撑以下的全部
子集，因此相对覆盖提升为所属模型全部对象的覆盖。像幂集的子集闭包还
回收目标的任意新子集；支撑处的原缺失子集不在这张对应图的定义域中。
最大强度仍由原证书的幂集像见证，所有比较都在原对象关系中完成。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.raw_strength_l {ω c' Y S Γ H k N S₀ z L b
    J O Z A p T V r o C W j D₀ a₀ f₀ H₁ : M.Domain}
    (hω : M.IsOmega ω) (model : Smdl_d I c' Y S) (ext : Rf_ext_d I Y S)
    (theory : Sc_theory_d I ω Y S)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := S₀) nx).Models ZF)
    (U₀ w ξ ℓ e β X' K' R' δ : (smdl_structure_l I (R := S₀) nx).Domain)
    (numbers : Rr_layer_d I ω N S₀ w.val z) (finite₀ : Fs_read_d w U₀)
    (products : ∀ m d : (smdl_structure_l I (R := S₀) nx).Domain,
      (smdl_structure_l I (R := S₀) nx).mem m w → Ep_space_d ξ m d →
      ∃ P : (smdl_structure_l I (R := S₀) nx).Domain, (smdl_structure_l I (R := S₀) nx).mem P U₀ ∧
        (smdl_structure_l I (R := S₀) nx).IsCartesianProduct (kp_pair_l (ZF.modelsKP hN)) P d β)
    (carrier₀ : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U₀.val S₀)
    (oc : Rr_closed_d I N S₀ U₀.val) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image₀ : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred₀ : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x S₀ ∧ Rd_entry_d s v k)
    (closed : Rr_closed_d I Y S H) (hβb : Rd_entry_d β.val b k)
    (hξU : (smdl_structure_l I (R := S₀) nx).mem ξ U₀)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hN)) w ξ K' X' R')
    (rank : V_d (kp_pair_l (ZF.modelsKP hN)) δ X')
    (height : (smdl_structure_l I (R := S₀) nx).IsLimitOrdinal δ)
    (powers₀ : Source_d U₀ ξ β) (strength : Ex_strength_d (kp_pair_l (ZF.modelsKP hN)) w ξ ℓ X' e)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val S₀)
    (system : Er_graph_d I ω L N S₀ ξ.val ℓ.val e.val z Y S k J O Z A p T V)
    (diagram : Di_system_d J O A p T V) (limit : Di_limit_d A p T V r C W)
    (next : Smdl_d I o C W) (embed : Smap_d I ω c' o Y C j) (hbH : Rd_entry_d b H₁ j)
    (ff₀ : Fn0_d D₀ Y f₀) (constant : Rs_const_d D₀ b f₀) (fv : Ep_repr_d r a₀ f₀ H₁)
    (loc : It_local_d I w.val N S₀ ξ.val ℓ.val e.val) :
    ∃ Z' : (smdl_structure_l I (R := S₀) nx).Domain,
      (smdl_structure_l I (R := S₀) nx).TransitiveSet Z' ∧ Es_strength_d X' ℓ Z' ∧
      ∃ Γ₁ t, (∀ x, M.mem x Γ₁ ↔ M.mem x N ∧ Rd_entry_d x Z'.val S₀) ∧
        M.IsSetInjectionFromTo I t Γ₁ C ∧
        (∀ E, Rd_entry_d E H₁ W ↔ ∃ x, M.mem x Γ₁ ∧ Rd_entry_d x E t) ∧
        (∀ x E, Rd_entry_d x E t → ∀ P, Rd_entry_d P E W ↔ ∃ y, Rd_entry_d y x S₀ ∧ Rd_entry_d y P t) ∧
        (∀ x y : (smdl_structure_l I (R := S₀) nx).Domain, ∀ E P,
          Rd_entry_d x.val E t → Rd_entry_d y.val P t →
            ((smdl_structure_l I (R := S₀) nx).mem x y ↔ Rd_entry_d E P W)) ∧
        Rr_closed_d I C W H₁ ∧
        (∀ α : (smdl_structure_l I (R := S₀) nx).Domain, ∀ A, Rd_entry_d α.val A t → ∀ E,
          (M.mem E C ∧ ∀ P, M.mem P C → Rd_entry_d P E W → Rd_entry_d P A W) ↔
            ∃ x : (smdl_structure_l I (R := S₀) nx).Domain,
              (smdl_structure_l I (R := S₀) nx).MemberSubset x α ∧ Rd_entry_d x.val E t) ∧
        (∀ α x : (smdl_structure_l I (R := S₀) nx).Domain,
          (smdl_structure_l I (R := S₀) nx).mem α ℓ →
          (smdl_structure_l I (R := S₀) nx).MemberSubset x α → ∃ E, Rd_entry_d x.val E t) ∧
        ∃ x : (smdl_structure_l I (R := S₀) nx).Domain,
          (smdl_structure_l I (R := S₀) nx).MemberSubset x ℓ ∧ ∀ E, ¬ Rd_entry_d x.val E t := by
  let N₀ := smdl_structure_l I (R := S₀) nx
  let KpN := kp_pair_l (ZF.modelsKP hN)
  -- 共同层的实际相对幂集识别所属模型的全幂集；原秩源包含它的全部成员。
  have fullPower (x : N₀.Domain) : N₀.mem x β ↔ N₀.MemberSubset x ξ :=
    ⟨fun hx => ((powers₀ x).mp hx).2, fun sub => (powers₀ x).mpr
      ⟨oc ξ.val x.val ξ.property x.property hξU (fun y hy hyx => sub ⟨y, hy⟩ hyx), sub⟩⟩
  have power : Source_d X' ξ β := fun x =>
    ⟨fun hx => ⟨v_subset_mem_l KpN rank source.cardinal_mem ((fullPower x).mp hx), (fullPower x).mp hx⟩,
      fun hx => (fullPower x).mpr hx.2⟩
  obtain ⟨_, _, hℓ, _, _, K₀, P₀, A', Q', Z', e', _, hP, _, finite, powers, owned, es⟩ := strength
  have eq := hN.1.eq_of_same_members K₀ K' (fun a => (finite a).trans ((source.finite_l (ZF.modelsKP hN)) a).symm)
  subst K₀
  have eq := hN.1.eq_of_same_members P₀ β (fun a => (powers a).trans (power a).symm)
  subst P₀
  have actual := loc.read_l I _ (kp_pair_l (ZF.modelsKP hN)) hN.1 w ξ ℓ e
  have nativeTrans : N₀.TransitiveSet β := fun x hx y hy => (power y).mpr
    ⟨source.transitive ξ source.cardinal_mem y (((power x).mp hx).2 y hy),
      actual.critical.1.transitive y (((power x).mp hx).2 y hy)⟩
  obtain ⟨D₁, Γ₁, s, v, t, _, carrier, _, _, _, _, _, _, _, ft, _, image, pred, _⟩ :=
    loc.raw_present_l hZF hω model ext theory nx (ZF.modelsKP hN) U₀ w ξ ℓ e numbers finite₀ carrier₀ oc
      fk image₀ pred₀ closed hξU length β X' K' δ A' Q' Z' e'
      products (source.finite_l (ZF.modelsKP hN)) source.finite.mem_l rank height hP nativeTrans owned
      system diagram limit next embed hβb hbH ff₀ constant fv
  have copy := owned
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, collapse, _⟩ := copy
  have atoms (x y : N₀.Domain) E P (hx : Rd_entry_d x.val E t) (hy : Rd_entry_d y.val P t) :
      N₀.mem x y ↔ Rd_entry_d E P W := by
    refine ⟨fun hxy => (pred y.val P hy E).mpr ⟨x.val, hxy, hx⟩, fun hEP => ?_⟩
    obtain ⟨z, hzy, hzE⟩ := (pred y.val P hy E).mp hEP
    have eq := ft.2 z x.val E hzE hx
    subst z
    exact hzy
  -- 原幂集的向下子集闭包沿实际常值嵌入传输，覆盖极限中的全部新子集。
  have closedB := rr_cross_closed_l I nx U₀ β finite₀.transitive carrier₀ fk image₀ pred₀ closed hβb
    (fun x y hx hy hxβ sub => (fullPower ⟨y, hy⟩).mpr (fun a ha =>
      (fullPower ⟨x, hx⟩).mp hxβ a (sub a.val a.property ha)))
  have closedH := (embed.rr_closed_l I hZF hω model next hbH).mp closedB
  refine ⟨Z', collapse.transitive, es, Γ₁, t, carrier, ft, image, pred, atoms, closedH, ?_, ?_, ?_⟩
  · intro α A hαA E
    constructor
    · rintro ⟨hE, sub⟩
      have hEH := closedH A E (ft.1.output_mem_of_pairMember hαA) hE
        ((image A).mpr ⟨α.val, ft.1.input_mem_of_pairMember hαA, hαA⟩) sub
      obtain ⟨x, hx, hxE⟩ := (image E).mp hEH
      let x' : N₀.Domain := ⟨x, ((carrier x).mp hx).1⟩
      refine ⟨x', fun y hy => ?_, hxE⟩
      have hyZ := collapse.transitive x' ((carrier x).mp hx).2 y hy
      obtain ⟨P, hP, hyP⟩ := ft.1.2.2 y.val ((carrier y.val).mpr ⟨y.property, hyZ⟩)
      exact (atoms y α P A hyP hαA).mpr (sub P hP ((atoms y x' P E hyP hxE).mp hy))
    · rintro ⟨x, sub, hxE⟩
      refine ⟨ft.1.output_mem_of_pairMember hxE, fun P _ hPE => ?_⟩
      obtain ⟨y, hyx, hyP⟩ := (pred x.val E hxE P).mp hPE
      let y' : N₀.Domain := ⟨y, ((carrier y).mp (ft.1.input_mem_of_pairMember hyP)).1⟩
      exact (atoms y' α P A hyP hαA).mp (sub y' hyx)
  · intro α x hα sub
    have hxX := v_subset_mem_l KpN rank (source.transitive ℓ hℓ α hα) sub
    obtain ⟨E, _, hxE⟩ := ft.1.2.2 x.val ((carrier x.val).mpr ⟨x.property, es.1 α hα x hxX sub⟩)
    exact ⟨E, hxE⟩
  · obtain ⟨x, _, sub, missing⟩ := es.2
    exact ⟨x, sub, fun E hxE => missing ((carrier x.val).mp (ft.1.input_mem_of_pairMember hxE)).2⟩

end YesMetaZFC.SetTheory.LargeCardinal
