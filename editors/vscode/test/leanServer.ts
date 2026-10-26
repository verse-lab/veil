// A Lean language server, spoken to as an LSP client would, for the tests of what Lean gives the
// extension through the editor, such as the code action with the config template of a module.
import { ChildProcess, spawn } from 'child_process';

interface Pending {
  resolve(result: unknown): void;
  reject(error: Error): void;
}

export class LeanServer {
  private readonly child: ChildProcess;
  private buffer = Buffer.alloc(0);
  private nextId = 1;
  private readonly pending = new Map<number, Pending>();
  private readonly listeners = new Set<(method: string, params: unknown) => void>();

  /** Start `lake serve` in the workspace `cwd` */
  constructor(cwd: string) {
    this.child = spawn('lake', ['serve'], { cwd, stdio: ['pipe', 'pipe', 'ignore'] });
    this.child.stdout?.on('data', (chunk: Buffer) => {
      this.buffer = Buffer.concat([this.buffer, chunk]);
      this.receive();
    });
  }

  private receive(): void {
    for (;;) {
      const headerEnd = this.buffer.indexOf('\r\n\r\n');
      if (headerEnd < 0) return;
      const length = Number(/Content-Length: (\d+)/i.exec(this.buffer.subarray(0, headerEnd).toString())?.[1]);
      const start = headerEnd + 4;
      if (this.buffer.length < start + length) return;
      const message = JSON.parse(this.buffer.subarray(start, start + length).toString('utf8'));
      this.buffer = this.buffer.subarray(start + length);
      if (message.id !== undefined && message.method !== undefined) {
        // A request of the server, e.g. to register a capability, which needs no answer here
        this.send({ jsonrpc: '2.0', id: message.id, result: null });
      } else if (message.id !== undefined) {
        const pending = this.pending.get(message.id);
        this.pending.delete(message.id);
        if (message.error) pending?.reject(new Error(`${message.error.message} (${message.error.code})`));
        else pending?.resolve(message.result);
      } else if (message.method !== undefined) {
        for (const listener of [...this.listeners]) listener(message.method, message.params);
      }
    }
  }

  /** The params of the next notification of `method` that `matches` */
  notification<T>(method: string, matches: (params: T) => boolean): Promise<T> {
    return new Promise(resolve => {
      const listener = (received: string, params: unknown) => {
        if (received !== method || !matches(params as T)) return;
        this.listeners.delete(listener);
        resolve(params as T);
      };
      this.listeners.add(listener);
    });
  }

  private send(message: object): void {
    const body = Buffer.from(JSON.stringify(message), 'utf8');
    this.child.stdin?.write(`Content-Length: ${body.length}\r\n\r\n`);
    this.child.stdin?.write(body);
  }

  request(method: string, params: unknown): Promise<unknown> {
    const id = this.nextId++;
    return new Promise((resolve, reject) => {
      this.pending.set(id, { resolve, reject });
      this.send({ jsonrpc: '2.0', id, method, params });
    });
  }

  notify(method: string, params: unknown): void {
    this.send({ jsonrpc: '2.0', method, params });
  }

  async close(): Promise<void> {
    try {
      await Promise.race([this.request('shutdown', null), new Promise(resolve => setTimeout(resolve, 5000))]);
      this.notify('exit', null);
    } finally {
      this.child.kill();
    }
  }
}
