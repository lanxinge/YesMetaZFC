import YesMetaZFC.Model.SetTheory.Internal.TypeRolesCode
import YesMetaZFC.Model.SetTheory.Internal.TypeTruth

/-! # 标签角色成为实际完整类型中的单个查询

查询只读原元组的坐标，不加入标签常量或元组对象参数。
在 Neeman §5 的 k+2 元组上，它正是所有 i<k 的 v_(i+1)=〈i,x〉。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tt_roles_query_l {ω n k U D : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω)
    (hk : M.mem k n) (pool : Tt_pool_d I ω n U D) : ∃ p, M.mem p D ∧
      ∀ c X R s δ t, Smem_d I c X R → M.TransitiveSet X →
        Tt_realized_d I ω c X R n s δ U D t → (M.mem p t ↔ Tr_roles_d I k s) := by
  -- 恒等名字列把原元组直接作为参数，不向常量池加入内部标签列。
  obtain ⟨N, E, names, seq, prod⟩ := pool
  let φ : BinarySchema 0 := { body := Formula.extensionalEq .newest (.bound 1) }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => n⟩
  have sat i j : φ.denote ρ i j ↔ j = i := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  obtain ⟨e, fn, column⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := n) (target := N)
    (fun i _ => ⟨i, (sat i i).mpr rfl⟩)
    (fun i _ x y hx hy => ((sat i x).mp hx).trans ((sat i y).mp hy).symm)
    (fun i j hi hj => ((sat i j).mp hj).symm ▸ (names i).mpr (Or.inl hi))
  have col i j : M.PairMember I i j e ↔ M.mem i n ∧ j = i := (column i j).trans (and_congr Iff.rfl (sat i j))
  obtain ⟨a, m, G, u, form, guard⟩ := tr_roles_build_l I hZF hω (hω.transitive hZF n hn k hk)
  obtain ⟨z, code⟩ := sc_num_exists_l I hZF hω form
  obtain ⟨p, hp⟩ := (I).total z e
  have hz := sc_num_natural_l I hZF hω code
  have hpD := (prod p).mpr ⟨z, hz, e, (seq e).mpr ⟨n, hn, fn⟩, hp⟩
  refine ⟨p, hpD, fun c X R s δ t model trans type => ?_⟩
  have tuple := fn0_function_l (ZF.modelsKP hZF) type.tuple
  have ord := hω.members_areOrdinals hZF n hn
  have assign : Tn_assign_d n s δ e s := by
    refine ⟨tuple.1.1, fun i x => ⟨?_, ?_⟩⟩
    · intro hx
      exact ⟨i, (col i i).mpr ⟨tuple.input_mem_of_pairMember hx, rfl⟩, Or.inl hx⟩
    · rintro ⟨j, hj, value⟩
      obtain ⟨hi, eq⟩ := (col i j).mp hj
      subst j
      obtain ⟨y, _, hy⟩ := tuple.2.2 i hi
      exact (tn_value_unique_l (ZF.modelsKP hZF) ord type.tuple value (Or.inl hy)).symm ▸ hy
  obtain ⟨f, fill, ff⟩ := senv_fill_exists_l I hZF tuple type.point
  -- k<n 保证所有被检查的 i+1 仍在原元组中，补齐赋值不改变查询。
  have bound {i j} (hi : M.mem i k) (hs : M.SuccessorOf j i) : M.mem j n := by
    apply ordinal_down_l (ZF.modelsKP hZF) (KP.successor_isOrdinal (ZF.modelsKP hZF) ((ord.mem hk).mem hi) hs) ord ?_ hk
    intro x hx
    rcases (hs x).mp hx with hx | hx
    · exact (ord.mem hk).transitive i hi x hx
    · exact (hZF.1.eq_of_same_members x i hx).symm ▸ hi
  have read i x (hi : M.mem i n) : M.PairMember I i x f ↔ M.PairMember I i x s :=
    (fill.2 i x).trans ⟨fun h => h.2.elim And.right (fun h => (h.1 hi).elim),
      fun h => ⟨hω.transitive hZF n hn i hi, Or.inl ⟨hi, h⟩⟩⟩
  have roles : Tr_roles_d I k f ↔ Tr_roles_d I k s :=
    ⟨fun h i j q hi hs hq => h i j q hi hs ((read j q (bound hi hs)).mpr hq),
      fun h i j q hi hs hq => h i j q hi hs ((read j q (bound hi hs)).mp hq)⟩
  exact (type.truth p).trans ((and_iff_right hpD).trans
    ((tt_query_decode_l I (ZF.modelsKP hZF) hp hz hn fn.2.1 assign fill).trans
      ((sc_sat_decode_l I hZF hω code).trans ((guard c X R f model trans ff).trans roles))))

end YesMetaZFC.SetTheory.Internal
