#include <string.h>
#include <ir/ir.h>
#include <target/util.h>

static void swift_emit_func_prologue(int func_id) {
  emit_line("");
  emit_line("private func func%d() {", func_id);
  inc_indent();
  emit_line("while %d <= pc && pc < %d {",
            func_id * CHUNKED_FUNC_SIZE, (func_id + 1) * CHUNKED_FUNC_SIZE);
  inc_indent();
  emit_line("switch pc {");
  emit_line("case -1:  /* dummy */");
  inc_indent();
  emit_line("break");
}

static void swift_emit_func_epilogue(void) {
  dec_indent();
  emit_line("default:");
  emit_line("  break");
  emit_line("}");
  emit_line("pc += 1");
  dec_indent();
  emit_line("}");
  dec_indent();
  emit_line("}");
}

static void swift_emit_pc_change(int pc) {
  emit_line("");
  dec_indent();
  emit_line("case %d:", pc);
  inc_indent();
}

static void swift_emit_inst(Inst* inst) {
  switch (inst->op) {
  case MOV:
    {
      const char *_l = reg_names[inst->dst.reg];
      const char *_r = src_str(inst);
      if (strcmp(_l, _r)) {
        emit_line("%s = %s", _l, _r);
        /* emit_line("%s = %s", reg_names[inst->dst.reg], src_str(inst)); */
      }
    }
    break;

  case ADD:
    emit_line("%s = (%s + %s) & " UINT_MAX_STR,
              reg_names[inst->dst.reg],
              reg_names[inst->dst.reg], src_str(inst));
    break;

  case SUB:
    emit_line("%s = (%s - %s) & " UINT_MAX_STR,
              reg_names[inst->dst.reg],
              reg_names[inst->dst.reg], src_str(inst));
    break;

  case LOAD:
    emit_line("%s = mem[%s]", reg_names[inst->dst.reg], src_str(inst));
    break;

  case STORE:
    emit_line("mem[%s] = %s", src_str(inst), reg_names[inst->dst.reg]);
    break;

  case PUTC:
    emit_line("print(\"\\(UnicodeScalar(%s)!)\", terminator:\"\")", src_str(inst));
    break;

  case GETC:
    emit_line("if true {");
    inc_indent();
    emit_line("let _c = getchar()");
    emit_line("%s = _c == -1 ? 0 : Int(_c)", reg_names[inst->dst.reg]);
    dec_indent();
    emit_line("}");
    break;

  case EXIT:
    emit_line("exit(0)");
    break;

  case DUMP:
    break;

  case EQ:
  case NE:
  case LT:
  case GT:
  case LE:
  case GE:
    emit_line("%s = %s ? 1 : 0",
              reg_names[inst->dst.reg], cmp_str(inst, "true"));
    break;

  case JEQ:
  case JNE:
  case JLT:
  case JGT:
  case JLE:
  case JGE:
  case JMP:
    emit_line("if %s { pc = %s - 1 }",
              cmp_str(inst, "true"), value_str(&inst->jmp));
    break;

  default:
    error("oops");
  }
}

static int swift_init_state(Data* data) {
  int prev_mc = -1;
  for (int mp = 0; data; data = data->next, mp++) {
    if (data->v) {
      int mc = mp / 1000;
      while (prev_mc != mc) {
        if (prev_mc != -1) {
          dec_indent();
          emit_line("}");
        }
        prev_mc++;
        emit_line("private func init%d() {", prev_mc);
        inc_indent();
      }
      emit_line("mem[%d] = %d", mp, data->v);
    }
  }

  if (prev_mc != -1) {
    dec_indent();
    emit_line("}");
  }

  return prev_mc + 1;
}

void target_swift(Module* module) {
  emit_line("import Foundation");
  for (int i = 0; i < 7; i++) {
    emit_line("private var %s: Int = 0", reg_names[i]);
  }
  emit_line("private var mem = [Int](repeating: 0, count: 1<<24)");

  int num_inits = swift_init_state(module->data);

  CHUNKED_FUNC_SIZE = 256;
  int num_funcs = emit_chunked_main_loop(module->text,
                                         swift_emit_func_prologue,
                                         swift_emit_func_epilogue,
                                         swift_emit_pc_change,
                                         swift_emit_inst);
  emit_line("");
  for (int i = 0; i < num_inits; i++) {
    emit_line("init%d()", i);
  }
  emit_line("");
  emit_line("while true {");
  inc_indent();
  emit_line("switch pc / %d | 0 {", CHUNKED_FUNC_SIZE);
  for (int i = 0; i < num_funcs; i++) {
    emit_line("case %d:", i);
    emit_line(" func%d()", i);
  }
  emit_line("default:");
  emit_line(" break");
  emit_line("}");
  dec_indent();
  emit_line("}");
}
