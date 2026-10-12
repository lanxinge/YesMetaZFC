import YesMetaZFC.Model.SetTheory.Internal.TypeGameNodeCode
import YesMetaZFC.Model.SetTheory.Internal.TypeColumn

/-! # 完整类型中的实际节点查询

查询码只依赖内部元数和低秩参数 s、t、k。所有原坐标保留为变量，
读出的是中间值的集合，而非预先指定的标签顺序。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tg_node_query_d (I : kpair_convention_l.Interpretation M) (ω e n l U D s t k q : M.Domain) : Prop :=
  M.mem q D ∧ ∀ c X R r δ T S, Smem_d I c X R → M.TransitiveSet X →
    Tt_realized_d I ω c X R n r δ U D T → Rd_entry_d e S r →
      (M.mem q T ↔ ∃ g, M.mem g X ∧ Sg_set_d I e l r g ∧ Tg_node_d I k S s t g)

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tt_node_query_l {ω e n l U D s t k : M.Domain} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hl : M.mem l n) (he : M.mem e l) (pool : Tt_pool_d I ω n U D)
    (hs : M.mem s U) (ht : M.mem t U) (hk : M.mem k U) :
    ∃ q, Tg_node_query_d I ω e n l U D s t k q := by
  obtain ⟨N, E, names, sequences, product⟩ := pool
  obtain ⟨b, σ, hb, nb, bound, _, columns⟩ := tt_column_build_l hZF hω hn 3
  let a : Fin 3 → M.Domain := Fin.cases s (Fin.cases t (fun _ => k))
  have ha : ∀ i, M.mem (a i) U := Fin.cases hs (Fin.cases ht (fun _ => hk))
  obtain ⟨v, hv⟩ := Classical.axiomOfChoice (fun i => (I).total (a i) (a i))
  obtain ⟨C, column, original, params⟩ := columns U N names v
    (fun i => (names (v i)).mpr (Or.inr (Or.inr ⟨a i, ha i, hv i⟩)))
  have ord := hω.members_areOrdinals hZF n hn
  have ln : M.MemberSubset l n := ord.transitive l hl
  obtain ⟨f, m, G, u, form, node⟩ := tg_node_build_l hZF hω (hω.transitive hZF n hn l hl) hb he
    (fun i hi => nb i (ln i hi)) σ bound
  obtain ⟨z, code⟩ := sc_num_exists_l I hZF hω form
  obtain ⟨q, cq⟩ := (I).total z C
  have hz := sc_num_natural_l I hZF hω code
  have hq := (product q).mpr ⟨z, hz, C, (sequences C).mpr ⟨b, hb, column⟩, cq⟩
  refine ⟨q, hq, fun c X R r δ T S model trans type rS => ?_⟩
  obtain ⟨r₁, assign, fr₁⟩ := tn_assign_exists_l hZF ord type.tuple type.point type.constants names
    (fn0_of_function_l (ZF.modelsKP hZF) column)
  obtain ⟨f₁, fill, ff₁⟩ := senv_fill_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) fr₁) type.point
  have value i j x (hj : Rd_entry_d i j C) (hx : Tn_value_d n r δ j x) : Rd_entry_d i x f₁ :=
    (fill.2 i x).mpr ⟨hω.transitive hZF b hb i (column.input_mem_of_pairMember hj),
      Or.inl ⟨column.input_mem_of_pairMember hj, (assign.2 i x).mpr ⟨j, hj, hx⟩⟩⟩
  have vars i x (hx : Rd_entry_d i x r) : Rd_entry_d i x f₁ :=
    value i i x (original i (type.tuple.bound_l hx).1) (Or.inl hx)
  have same i x (hi : M.mem i n) : Rd_entry_d i x r ↔ Rd_entry_d i x f₁ := by
    refine ⟨vars i x, fun hx => ?_⟩
    obtain ⟨y, _, hy⟩ := type.tuple.2.1 i hi
    exact ff₁.1.2 i y x (vars i y hy) hx ▸ hy
  have sets g : Sg_set_d I e l f₁ g ↔ Sg_set_d I e l r g :=
    forall_congr' fun x => iff_congr Iff.rfl (exists_congr fun i => and_congr_right fun hi =>
      and_congr_right fun _ => (same i x (ln i hi)).symm)
  have constants i : Rd_entry_d (σ i) (a i) f₁ := value (σ i) (v i) (a i) (params i) (Or.inr (Or.inr (hv i)))
  exact (type.truth q).trans ((and_iff_right hq).trans
    ((tt_query_decode_l I (ZF.modelsKP hZF) cq hz hb column.2.1 assign fill).trans
      ((sc_sat_decode_l I hZF hω code).trans
        ((node c X R f₁ S s t k model trans ff₁ (vars e S rS) (constants 0) (constants 1) (constants 2)).trans
          (exists_congr fun g => and_congr Iff.rfl (and_congr (sets g) Iff.rfl))))))

end YesMetaZFC.SetTheory.Internal
