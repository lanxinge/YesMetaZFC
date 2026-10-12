import YesMetaZFC.Model.SetTheory.Internal.TypeColumn
import YesMetaZFC.Model.SetTheory.Internal.TuplePackBinder

/-! # 先于具体常量固定的内部查询程序

槽位表与程序只取决于内部元数和句子模板。实际名字列随后填入，
同一程序对每个合法名字列成立，因此可以连同列关系一起沿嵌入运输。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

structure Tt_packed_d (ω n : M.Domain) {k : Nat} (φ : Formula 1 (k+1)) (j : Fin k)
    (b : M.Domain) (σ : Fin k → M.Domain) (a z : M.Domain) : Prop where
  finite : M.mem n ω
  length : M.mem b ω
  natural : M.mem z ω
  prefix_bound : M.MemberSubset n b
  slots : ∀ i, M.mem (σ i) b
  cover : ∀ i, M.mem i b → M.mem i n ∨ ∃ j, i = σ j
  columns : ∀ U N, Tn_names_d n U N → ∀ v : Fin k → M.Domain, (∀ i, M.mem (v i) N) →
    ∃ C, M.IsSetFunctionFromTo Q C b N ∧ (∀ i, M.mem i n → Rd_entry_d i i C) ∧
      ∀ i, Rd_entry_d (σ i) (v i) C
  code : Sc_num_d Q ω a z
  compile : ∀ η Y c R f g (model : Smem_d Q c Y R)
      (ρ : Env (smdl_structure_l Q (R := R) model.1.2.1) k),
    V_d Q η Y → M.mem ω Y → M.IsSetFunctionFromTo Q f ω Y → M.IsSetFunctionFromTo K g ω Y →
    Sx_graph_d Q K f g → Rd_entry_d (σ j) ω f → (∀ i, Rd_entry_d (σ i) (ρ.bound i).val f) →
      (Satisfies_d Q ω c a f ↔ ∃ p : (smdl_structure_l Q (R := R) model.1.2.1).Domain,
        Fs_code_d K ω Y g n p.val ∧ Formula.satisfies (ρ.push p) φ)

theorem tt_packed_program_l {ω n : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω)
    {k : Nat} (φ : Formula 1 (k+1)) (hc : φ.FreeClosed) (j : Fin k) :
    ∃ b σ a z, Tt_packed_d hZF ω n φ j b σ a z := by
  obtain ⟨b, σ, hb, nb, bounds, cover, columns⟩ := tt_column_build_l hZF hω hn k
  obtain ⟨a, m, G, u, form, compile⟩ := st_pack_bind_l hZF hω hb (bounds j) hn nb φ hc σ bounds
  obtain ⟨z, code⟩ := sc_num_exists_l Q hZF hω form
  exact ⟨b, σ, a, z, hn, hb, sc_num_natural_l Q hZF hω code, nb, bounds, cover, columns, code, compile⟩

theorem Tt_packed_d.query_l {ω n U N D b a z q C : M.Domain} (hω : M.IsOmega ω)
    {k : Nat} {φ : Formula 1 (k+1)} {j : Fin k} {σ : Fin k → M.Domain}
    (prog : Tt_packed_d hZF ω n φ j b σ a z) (pool : Tt_pool_d Q ω n U D) (names : Tn_names_d n U N)
    (v : Fin k → M.Domain) (column : M.IsSetFunctionFromTo Q C b N)
    (original : ∀ i, M.mem i n → Rd_entry_d i i C) (params : ∀ i, Rd_entry_d (σ i) (v i) C)
    (pair : (Q).Codes q z C) :
    M.mem q D ∧ ∀ η Y c R s δ t (model : Smem_d Q c Y R)
      (_type : Tt_realized_d Q ω c Y R n s δ U D t) (ρ : Env (smdl_structure_l Q (R := R) model.1.2.1) k),
      V_d Q η Y → (∀ i, Tn_value_d n s δ (v i) (ρ.bound i).val) → (ρ.bound j).val = ω →
        (M.mem q t ↔ ∃ g, M.IsSetFunctionFromTo K g ω Y ∧
          (∀ i x, M.mem i n → (Rd_entry_d i x s ↔ M.PairMember K i x g)) ∧
          ∃ p : (smdl_structure_l Q (R := R) model.1.2.1).Domain,
            Fs_code_d K ω Y g n p.val ∧ Formula.satisfies (ρ.push p) φ) := by
  obtain ⟨N', E, names', sequences, product⟩ := pool
  have eqN := hZF.1.eq_of_same_members N' N (fun x => (names' x).trans (names x).symm)
  subst N'
  have hz := prog.natural
  have hq := (product q).mpr ⟨z, hz, C, (sequences C).mpr ⟨b, prog.length, column⟩, pair⟩
  refine ⟨hq, fun η Y c R s δ t model type ρ hY values hw => ?_⟩
  have hωY : M.mem ω Y := hw ▸ (ρ.bound j).property
  obtain ⟨r, assign, fr⟩ := tn_assign_exists_l hZF (hω.members_areOrdinals hZF n prog.finite)
    type.tuple type.point type.constants names (fn0_of_function_l (ZF.modelsKP hZF) column)
  obtain ⟨f, fill, ff⟩ := senv_fill_exists_l Q hZF (fn0_function_l (ZF.modelsKP hZF) fr) type.point
  have value i a x (ha : Rd_entry_d i a C) (hx : Tn_value_d n s δ a x) : Rd_entry_d i x f :=
    (fill.2 i x).mpr ⟨hω.transitive hZF b prog.length i (column.input_mem_of_pairMember ha),
      Or.inl ⟨column.input_mem_of_pairMember ha, (assign.2 i x).mpr ⟨a, ha, hx⟩⟩⟩
  have vars i x (hx : Rd_entry_d i x s) : Rd_entry_d i x f :=
    value i i x (original i (type.tuple.bound_l hx).1) (Or.inl hx)
  have orig i x (hi : M.mem i n) : Rd_entry_d i x s ↔ Rd_entry_d i x f := by
    refine ⟨vars i x, fun hx => ?_⟩
    obtain ⟨y, _, hy⟩ := type.tuple.2.1 i hi
    exact ff.1.2 i y x (vars i y hy) hx ▸ hy
  obtain ⟨g, fg, agree⟩ := fn_recode_l Q K hZF ff
  have same i x hi := (orig i x hi).trans (agree i x).symm
  have read := (type.truth q).trans ((and_iff_right hq).trans
    ((tt_query_decode_l Q (ZF.modelsKP hZF) pair hz prog.length column.2.1 assign fill).trans
      ((sc_sat_decode_l Q hZF hω prog.code).trans
        (prog.compile η Y c R f g model ρ hY hωY ff fg agree
          (hw ▸ value (σ j) (v j) (ρ.bound j).val (params j) (values j))
          (fun i => value (σ i) (v i) (ρ.bound i).val (params i) (values i))))))
  refine read.trans ⟨fun ⟨p, cp, truth⟩ => ⟨g, fg, same, p, cp, truth⟩, ?_⟩
  rintro ⟨g', fg', same', p, cp, truth⟩
  have hωη := (v_ordinal_l Q hY).transitive ω (ZF.v_ordinal_height_l hZF hY (hω.isOrdinal hZF) hωY)
  obtain ⟨H, trace, _⟩ := fp_trace_rank_l Q hZF hω hY hωη fg
  exact ⟨p, cp.transport_l K hZF hω fg' fg trace (fun i x hi => (same' i x hi).symm.trans (same i x hi)), truth⟩

end YesMetaZFC.SetTheory.Internal
