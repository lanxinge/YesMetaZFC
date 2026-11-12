import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawEvaluation
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawConstant

/-! # 原对象码后继的未坍塌极限

全部支撑的实际定向系统直接进入原关系极限。当前源经空支撑常值分量
初等嵌入同一极限；原始给定模型的复合嵌入直接给出极限的原关系源理论及小定义域收集，
完整内部 ZFC 证书也沿同一图保持。
共同切片中每个对象的常值像，其全部成员与所属有界函数双向对应。
所属结构只需 KP、有限幂的实际幂集及两个有限幂的乘积。指定值域的反向
函数回收另只读取该值域所需的乘积；极限构造不要求整个共同层的乘积闭包。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.code_limit_l {ω c X R c' Y S q Γ H k N T z : M.Domain}
    (hω : M.IsOmega ω) (ex : Rf_ext_d Kp X R) (mx : Smdl_d Kp c X R)
    (theory : Sc_theory_d Kp ω X R) (collection : Sc_collection_d Kp ω X R)
    (model : Smdl_d Kp c' Y S) (hq : Smap_d Kp ω c c' X Y q)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l Kp (R := T) nx).Models KP)
    (U w ξ ℓ f : (smdl_structure_l Kp (R := T) nx).Domain)
    (numbers : Rr_layer_d Kp ω N T w.val z) (finite : Fs_read_d w U)
    (powers : ∀ m d : (smdl_structure_l Kp (R := T) nx).Domain,
      (smdl_structure_l Kp (R := T) nx).mem m w → Ep_space_d ξ m d →
        ∃ p, (smdl_structure_l Kp (R := T) nx).IsPowerSetOf p d)
    (products : ∀ m n d e : (smdl_structure_l Kp (R := T) nx).Domain,
      (smdl_structure_l Kp (R := T) nx).mem m w → (smdl_structure_l Kp (R := T) nx).mem n w →
      Ep_space_d ξ m d → Ep_space_d ξ n e → ∃ B,
        (smdl_structure_l Kp (R := T) nx).mem B U ∧ (smdl_structure_l Kp (R := T) nx).IsCartesianProduct (kp_pair_l hN) B d e)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (ownerClosed : Rr_closed_d Kp N T U.val) (fk : M.IsSetInjectionFromTo Kp k Γ Y)
    (image : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (closed : Rr_closed_d Kp Y S H) (small : Rr_small_d Kp Y S H)
    (hξ : (smdl_structure_l Kp (R := T) nx).mem ξ U)
    (loc : It_local_d Kp w.val N T ξ.val ℓ.val f.val) :
    ∃ L J O Z A p V W r o C U' i q',
      (∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T) ∧
      Er_graph_d Kp ω L N T ξ.val ℓ.val f.val z Y S k J O Z A p V W ∧
      Di_system_d J O A p V W ∧ Di_limit_d A p V W r C U' ∧ Smdl_d Kp o C U' ∧ Sc_theory_d Kp ω C U' ∧ Sc_collection_d Kp ω C U' ∧
      Di_elementary_d Kp ω O A p V W ∧ Smap_d Kp ω c' o Y C i ∧ Smap_d Kp ω c o X C q' ∧
      Er_constants_d Y r i ∧
      (Zc_model_d Kp ω c X R → Zc_model_d Kp ω o C U') ∧
      (∀ x E, Rd_entry_d x E q' ↔ M.mem x X ∧ ∃ y, Rd_entry_d x y q ∧ Rd_entry_d y E i) ∧
      ∃ a D, (∀ x, ¬ M.mem x a) ∧
        (∀ x E, Rd_entry_d x E i → ∃ B g u,
          Fn0_d D Y g ∧ M.mem g B ∧ Rs_const_d D x g ∧ KPair_d M u a B ∧ Rd_entry_d u E r) ∧
        (∀ β : (smdl_structure_l Kp (R := T) nx).Domain, ∀ b H₀ E,
          Rd_entry_d β.val b k → Rd_entry_d b H₀ i → Rd_entry_d E H₀ U' →
          (∀ m d : (smdl_structure_l Kp (R := T) nx).Domain,
            (smdl_structure_l Kp (R := T) nx).mem m w → Ep_space_d ξ m d → ∃ P,
              (smdl_structure_l Kp (R := T) nx).mem P U ∧
                (smdl_structure_l Kp (R := T) nx).IsCartesianProduct (kp_pair_l hN) P d β) →
          ∃ α, ∃ m α' d f' : (smdl_structure_l Kp (R := T) nx).Domain, ∃ D' F g,
            M.mem α J ∧ Rr_finite_d Kp ω L N T z α α'.val ∧ (smdl_structure_l Kp (R := T) nx).mem m w ∧
            Fn0_d m ℓ α' ∧ Ep_space_d ξ m d ∧ (smdl_structure_l Kp (R := T) nx).mem f' U ∧ Fn0_d d β f' ∧
            (∀ s, M.mem s D' ↔ M.mem s N ∧ Rd_entry_d s d.val T) ∧ Fn0_d D' Γ F ∧
            (∀ s v : (smdl_structure_l Kp (R := T) nx).Domain, Rd_entry_d s.val v.val F ↔ Rd_entry_d s v f') ∧
            Cp0_d D' Γ Y F k g ∧ Ep_repr_d r α g E) ∧
        ∀ β : (smdl_structure_l Kp (R := T) nx).Domain, ∀ b H₀,
          Rd_entry_d β.val b k → Rd_entry_d b H₀ i → ∀ α,
          ∀ m α' d f' : (smdl_structure_l Kp (R := T) nx).Domain,
            M.mem α J → Rr_finite_d Kp ω L N T z α α'.val → Fn0_d m ℓ α' → Ep_space_d ξ m d →
            (smdl_structure_l Kp (R := T) nx).mem f' U → Fn0_d d β f' →
            ∃ D' F g E, (∀ s, M.mem s D' ↔ M.mem s N ∧ Rd_entry_d s d.val T) ∧ Fn0_d D' Γ F ∧
              (∀ s v : (smdl_structure_l Kp (R := T) nx).Domain, Rd_entry_d s.val v.val F ↔ Rd_entry_d s v f') ∧
              Cp0_d D' Γ Y F k g ∧ Ep_repr_d r α g E ∧ Rd_entry_d E H₀ U' := by
  obtain ⟨L, J, O, Z, A, p, V, W, length, h, diagram⟩ :=
    loc.code_system_l hZFC hω ex mx theory collection model hq nx hN U w ξ ℓ f
      numbers finite powers products carrier ownerClosed fk image pred closed small hξ
  have elementary := h.elementary_l hZF hω
  obtain ⟨Q, table⟩ := h.codes
  -- 空支撑只指定常值嵌入的入口；整个系统仍包含全部内部有限支撑。
  obtain ⟨a, empty, haω⟩ := hω.1.1
  have fa : Fn0_d a L a := ⟨fun x hx => (empty x hx).elim, fun x hx => (empty x hx).elim,
    fun x hx => (empty x hx).elim⟩
  have inj i j x (hi : Rd_entry_d i x a) (_ : Rd_entry_d j x a) : i = j :=
    hi.elim fun p hp => (empty p hp.2).elim
  have ha := (h.indices a).mpr ⟨a, haω, fa, inj⟩
  obtain ⟨o₀, _, hao⟩ := table.2.1 a ha
  obtain ⟨C₀, W₀, i₀, D, m₀, hi₀, constants⟩ :=
    (h.components a o₀ hao).constant_l hZF hω ex mx theory collection model hq nx hN U w ξ ℓ f
      numbers finite powers carrier ownerClosed fk image pred closed small hξ length loc
  obtain ⟨B₀, hB₀⟩ := m₀.2.1
  obtain ⟨u, pair⟩ := (Kp).total a B₀
  have hu := (h.nodes u).mpr ⟨a, B₀, pair, o₀, C₀, W₀, hao, m₀.1, hB₀⟩
  obtain ⟨o, r, C, U', limit, mc⟩ := di_model_exists_l hZF diagram ⟨u, hu⟩
  obtain ⟨v, hv, values⟩ := h.stage_l hZF hω diagram limit mc hao m₀
  obtain ⟨i, hi, square⟩ := smap_comp_l Kp hZF hi₀ hv
  obtain ⟨q', hq', composition⟩ := smap_comp_l Kp hZF hq hi
  have representatives x E (hxE : Rd_entry_d x E i) : ∃ B g u,
      Fn0_d D Y g ∧ M.mem g B ∧ Rs_const_d D x g ∧ KPair_d M u a B ∧ Rd_entry_d u E r := by
    obtain ⟨_, B, hxB, hBE⟩ := (square x E).mp hxE
    obtain ⟨_, _, g, fg, hg, constant⟩ := (constants x B).mp hxB
    obtain ⟨_, u, pair, huE⟩ := (values B E).mp hBE
    exact ⟨B, g, u, fg, hg, constant, pair, huE⟩
  have constants : Er_constants_d Y r i := by
    intro x E hxE
    obtain ⟨B, g, u, fg, hg, constant, pair, huE⟩ := representatives x E hxE
    exact ⟨a, D, g, fg, constant, u, B, pair, hg, huE⟩
  have ext : Rf_ext_d Kp C U' := hq'.extensional_l hZF hω mx mc ex
  have currentExt : Rf_ext_d Kp Y S := hq.extensional_l hZF hω mx model ex
  have current := theory.map_l Kp hZF hω mx model hq
  have collect := collection.map_l Kp hZF hω mx mc
    (ex.native_l Kp mx.2.1) (ext.native_l Kp mc.2.1) hq'
  refine ⟨L, J, O, Z, A, p, V, W, r, o, C, U', i, q', length, h, diagram, limit, mc,
    theory.map_l Kp hZF hω mx mc hq', collect, elementary, hi, hq', constants, (fun certificate => certificate.map_l hZF hω mc hq'), composition,
    a, D, empty, representatives, ?_, ?_⟩
  · intro β b H₀ E hβb hbH edge boundProducts
    obtain ⟨B, g, u, fg, hg, constant, pair, huH⟩ := representatives b H₀ hbH
    exact h.bounded_l hZF hω model currentExt current nx hN U w ξ ℓ f β numbers finite powers carrier ownerClosed
      fk image pred closed hξ length boundProducts diagram limit hβb
      fg constant ⟨u, B, pair, hg, huH⟩ edge loc
  · intro β b H₀ hβb hbH α m α' d f' hα code fa space hf fn
    obtain ⟨D', F, g, E, dc, fF, graph, comp, value, bound⟩ := h.bounded_value_l hZF hω model currentExt current
      nx hN U w ξ ℓ f β numbers finite powers carrier ownerClosed fk image pred closed hξ length limit hβb
      m α' d f' hα code fa space hf fn loc
    obtain ⟨B, g₀, u, fg₀, hg₀, constant, pair, huH⟩ := representatives b H₀ hbH
    exact ⟨D', F, g, E, dc, fF, graph, comp, value,
      h.bound_mem_l hZF hω mx theory model hq nx hN U w ξ ℓ f numbers finite powers carrier ownerClosed
        fk image pred closed hξ length diagram limit (fk.1.output_mem_of_pairMember hβb)
        fg₀ constant ⟨u, B, pair, hg₀, huH⟩ bound value loc⟩

end YesMetaZFC.SetTheory.LargeCardinal
